/**

    Setup for writing rules for Aave Token v3 

*/

/**
    Public methods from the AaveTokenV3Harness.sol
*/

methods{
    totalSupply() returns (uint256) envfree
    balanceOf(address addr) returns (uint256) envfree
    transfer(address to, uint256 amount) returns (bool)
    transferFrom(address from, address to, uint256 amount) returns (bool)
    delegate(address delegatee)
    metaDelegate(address, address, uint256, uint8, bytes32, bytes32)
    getPowerCurrent(address user, uint8 delegationType) returns (uint256) envfree
    getBalance(address user) returns (uint104) envfree
    getDelegatedPropositionBalance(address user) returns (uint72) envfree
    getDelegatedVotingBalance(address user) returns (uint72) envfree
    getDelegatingProposition(address user) returns (bool) envfree
    getDelegatingVoting(address user) returns (bool) envfree
    getVotingDelegate(address user) returns (address) envfree
    getPropositionDelegate(address user) returns (address) envfree
    delegateByType(address delegatee, uint8 delegationType)
    metaDelegateByType(address, address, uint8, uint256, uint8, bytes32, bytes32)
    _governancePowerTransferByType(uint104, uint104, address, uint8)
    getDelegationState(address user) returns (uint8) envfree
}

/**

    Constants

*/
// GovernancyType enum from the token contract
definition VOTING_POWER() returns uint8 = 0;
definition PROPOSITION_POWER() returns uint8 = 1;

// DelegationState enum from the BaseAaveToken contract
definition NO_DELEGATION() returns uint8 = 0;
definition VOTING_DELEGATED() returns uint8 = 1;
definition PROPOSITION_DELEGATED() returns uint8 = 2;
definition FULL_POWER_DELEGATED() returns uint8 = 3;

definition DELEGATED_POWER_DIVIDER() returns uint256 = 10^10;

// 16000000 * 10^18 is the maximum supply of the AAVE token
definition MAX_DELEGATED_BALANCE() returns uint256 = 16000000 * 10^18 / DELEGATED_POWER_DIVIDER();

/**

    Function that normalizes (removes 10 least significant digits) a given param. 
    It mirrors the way delegated balances are stored in the token contract. Since the delegated
    balance is stored as a uint72 variable, delegated amounts (uint256()) are normalized.

*/

function normalize(uint256 amount) returns uint256 {
    return to_uint256(amount / DELEGATED_POWER_DIVIDER() * DELEGATED_POWER_DIVIDER());
}

function normalize_72(uint256 amount) returns uint256 {
    return to_uint256(amount / DELEGATED_POWER_DIVIDER());
}

// rule MethodsVacuityCheck(method f) {
// 	env e; calldataarg args;
// 	f(e, args);
// 	assert false, "this method should have a non reverting path";
// }

/**

    Testing correctness of delegate(). An example of a unit test

*/

rule delegateCorrectness(address bob) {
    env e;
    // delegate not to self or to zero
    require bob != e.msg.sender && bob != 0;

    uint256 bobDelegatedBalance = getDelegatedVotingBalance(bob);
    // avoid unrealistic delegated balance
    require(bobDelegatedBalance < MAX_DELEGATED_BALANCE());
    
    // verify that the sender doesn't already delegate to bob
    address delegateBefore = getVotingDelegate(e.msg.sender);
    require delegateBefore != bob;

    uint256 bobVotingPowerBefore = getPowerCurrent(bob, VOTING_POWER());
    uint256 delegatorBalance = balanceOf(e.msg.sender);

    delegate(e, bob);

    // test the delegate indeed has changed to bob
    address delegateAfter = getVotingDelegate(e.msg.sender);
    assert delegateAfter == bob;

    // test the delegate's new voting power
    uint256 bobVotingPowerAfter = getPowerCurrent(bob, VOTING_POWER());
    assert bobVotingPowerAfter == bobVotingPowerBefore + normalize(delegatorBalance);
}

/**

    Verify that only delegate functions can change someone's delegate.
    An example for a parametric rule.

*/

rule votingDelegateChanges(address alice, method f) {
    env e;
    calldataarg args;

    address aliceDelegateBefore = getVotingDelegate(alice);

    f(e, args);

    address aliceDelegateAfter = getVotingDelegate(alice);

    // only these four function may change the delegate of an address
    assert aliceDelegateAfter != aliceDelegateBefore =>
        f.selector == delegate(address).selector || 
        f.selector == delegateByType(address,uint8).selector ||
        f.selector == metaDelegate(address,address,uint256,uint8,bytes32,bytes32).selector ||
        f.selector == metaDelegateByType(address,address,uint8,uint256,uint8,bytes32,bytes32).selector;
}

/**

    A ghost variable that tracks the sum of all addresses' balances

*/
ghost mathint sumBalances {
    init_state axiom sumBalances == 0;
}

/**

    This hook updates the sumBalances ghost whenever any address balance is updated

*/
hook Sstore _balances[KEY address user].balance uint104 balance
    (uint104 old_balance) STORAGE {
        sumBalances = sumBalances - to_mathint(old_balance) + to_mathint(balance);
    }

/**

    Invariant: 
    sum of all addresses' balances should be always equal to the total supply of the token
    
*/
invariant totalSupplyEqualsBalances()
    sumBalances == totalSupply()

/**

    RULE 1

    Condition: Account is not receiving delegation of power from anybody and that account is not delegating that power to anybody
    Checks: VOTING_POWER
    Checks Methods: All
    Outcome: PASSES

    Testing that the power of the account is equal to its AAVE balance for delegation type VOTING_POWER

    Note: assert false checked for vacuity

*/
rule votingPowerOfAccountEqualToAaveBalance(address account, method f) {

    calldataarg args;
    env e;

    // ====== Requirements of account ======

    // Require power before is equal to balance before
    uint256 accountPowerBefore = getPowerCurrent(account, VOTING_POWER());
    uint256 accountBalanceBefore = balanceOf(account);
    require accountPowerBefore == accountBalanceBefore;

    // Require account is not delegatee of sender
    address delegateeOfSenderBefore = getVotingDelegate(e.msg.sender);
    require delegateeOfSenderBefore != account;

    // Require delegated voting balance of account is zero 
    uint72 delegatedVotingBalance = getDelegatedVotingBalance(account);
    require delegatedVotingBalance == 0;

    // Require delegation state of account is NO_DELEGATION 
    uint8 delegationState = getDelegationState(account);
    require delegationState == NO_DELEGATION();

    if (f.selector == delegate(address).selector) {

        // ===== Variables for this method ======
        env e_delegate;
        address delegatee_delegate;

        // ====== Requirements for this method ======

        // Require account is not delegatee of sender
        address delegateeOfSenderBefore_delegate = getVotingDelegate(e_delegate.msg.sender);
        require delegateeOfSenderBefore_delegate != account;

        // Require account is not the delegatee
        require delegatee_delegate != account;

        // Require account does not call delegate methods
        require e_delegate.msg.sender != account;

         // ====== Method ======
        delegate(e_delegate, delegatee_delegate);

    } else if (f.selector == delegateByType(address, uint8).selector) {

        // ===== Variables for this method ======
        env e_delegateByType;
        address delegatee_delegateByType;

        // ====== Requirements for this method ======

        // Require account is not delegatee of sender
        address delegateeOfSenderBefore_delegateByType = getVotingDelegate(e_delegateByType.msg.sender);
        require delegateeOfSenderBefore_delegateByType != account;

        // Require account is not the delegatee
        require delegatee_delegateByType != account;

        // Require account does not call delegate methods
        require e_delegateByType.msg.sender != account;

        // ====== Method ======
        delegateByType(e_delegateByType, delegatee_delegateByType, VOTING_POWER());

    } else if (f.selector == metaDelegate(address, address, uint256, uint8, bytes32, bytes32).selector) {

        // ===== Variables for this method ======
        env e_metaDelegate;
        address delegatee_metaDelegate;
        address delegator_metaDelegate;
        uint256 deadline_metaDelegate;
        uint8 v_metaDelegate;
        bytes32 r_metaDelegate;
        bytes32 s_metaDelegate;

        // ====== Requirements for this method ======

        // Require account is not the delegatee
        require delegatee_metaDelegate != account;

        // Require account is not the delegator 
        require delegator_metaDelegate != account;

        // Require account is not delegatee of the delegator
        address delegateeOfDelegatorBefore_metaDelegate = getVotingDelegate(delegator_metaDelegate);
        require delegateeOfDelegatorBefore_metaDelegate != account;

        // ====== Method ======
        metaDelegate(e_metaDelegate, delegator_metaDelegate, delegatee_metaDelegate,deadline_metaDelegate,v_metaDelegate,r_metaDelegate,s_metaDelegate);
    
    } else if (f.selector == metaDelegateByType(address, address, uint8, uint256, uint8, bytes32, bytes32).selector) {
        
        // ===== Variables for this method ======
        env e_metaDelegateByType;
        address delegatee_metaDelegateByType;
        address delegator_metaDelegateByType;
        uint256 deadline_metaDelegateByType;
        uint8 v_metaDelegateByType;
        bytes32 r_metaDelegateByType;
        bytes32 s_metaDelegateByType;

        // ====== Requirements for this method ======

        // Require account is not the delegatee
        require delegatee_metaDelegateByType != account;

        // Require account is not the delegator 
        require delegator_metaDelegateByType != account;

        // Require account is not delegatee of the delegator
        address delegateeOfDelegatorBefore_metaDelegateByType = getVotingDelegate(delegator_metaDelegateByType);
        require delegateeOfDelegatorBefore_metaDelegateByType != account;
        
        // ====== Method ======
        metaDelegateByType(e_metaDelegateByType, delegator_metaDelegateByType, delegatee_metaDelegateByType, VOTING_POWER(), deadline_metaDelegateByType, v_metaDelegateByType, r_metaDelegateByType, s_metaDelegateByType);

    } else if (f.selector == _governancePowerTransferByType(uint104, uint104, address, uint8).selector) {

         // ===== Variables for this method ======
        env e_governancePowerTransferByType;
        address delegatee_governancePowerTransferByType;
        uint104 impactOnDelegationBefore;
        uint104 impactOnDelegationAfter;

        // ====== Requirements for this method ======

        // Require account is not the delegatee
        require delegatee_governancePowerTransferByType != account;

        // ====== Method ======
        _governancePowerTransferByType(e_governancePowerTransferByType, impactOnDelegationBefore, impactOnDelegationBefore, delegatee_governancePowerTransferByType, VOTING_POWER());

    } else if (f.selector == transfer(address, uint256).selector) {

        // ===== Variables for this method ======
        env e_transfer;
        address to_transfer;
        uint256 amount_transfer;

        // ====== Requirements for this method ======

        // Require account is not the delegatee of the sender
        address delegateeOfSenderBefore_transfer = getVotingDelegate(e_transfer.msg.sender);
        require delegateeOfSenderBefore_transfer != account;

        // Require account is not delegatee of "to" account
        address votingDelegatee_transfer = getVotingDelegate(to_transfer);
        require votingDelegatee_transfer != account;

        // ====== Method ======
        transfer(e_transfer, to_transfer, amount_transfer);

    } else if (f.selector == transferFrom(address, address, uint256).selector) {
        // ===== Variables for this method ======
        env e_transferFrom;
        address to_transferFrom;
        address from_transferFrom;
        uint256 amount_transferFrom;

        // ====== Requirements for this method ======

        // Require account is not the delegatee of the sender
        address delegateeOfSenderBefore_transferFrom = getVotingDelegate(e_transferFrom.msg.sender);
        require delegateeOfSenderBefore_transferFrom != account;

        // Require account is not delegatee of "to" account
        address votingDelegatee_transferFrom = getVotingDelegate(to_transferFrom);
        require votingDelegatee_transferFrom  != account;

        // ====== Method ======
        transferFrom(e_transferFrom, from_transferFrom, to_transferFrom, amount_transferFrom);
    }

    else {
        // ====== Run all other methods ======
        f(e, args);
    }

    uint256 accountPowerAfter = getPowerCurrent(account, VOTING_POWER());
    uint256 accountBalanceAfter = balanceOf(account);

    assert accountPowerAfter == accountBalanceAfter, "Power of account must be equal to its AAVE Balance when account is not delegating nor being delegated to";
}

/**

    RULE 2

    Condition: Account is not receiving delegation of power from anybody and that account is not delegating that power to anybody
    Checks: PROPOSITION_POWER
    Checks Methods: All
    Outcome: PASSES

    Testing that the power of the account is equal to its AAVE balance for delegation type PROPOSITION_POWER

    Note: assert false checked for vacuity

*/
rule propositionPowerOfAccountEqualToAaveBalance(address account, method f) {

    calldataarg args;
    env e;

    // ====== Requirements of account ======

    // Require power before is equal to balance before
    uint256 accountPowerBefore = getPowerCurrent(account, PROPOSITION_POWER());
    uint256 accountBalanceBefore = balanceOf(account);
    require accountPowerBefore == accountBalanceBefore;

    // Require account is not delegatee of sender
    address delegateeOfSenderBefore = getPropositionDelegate(e.msg.sender);
    require delegateeOfSenderBefore != account;

    // Require delegated Proposition balance of account is zero 
    uint72 delegatedPropositionBalance = getDelegatedPropositionBalance(account);
    require delegatedPropositionBalance == 0;

    // Require delegation state of account is NO_DELEGATION 
    uint8 delegationState = getDelegationState(account);
    require delegationState == NO_DELEGATION();

    if (f.selector == delegate(address).selector) {

        // ===== Variables for this method ======
        env e_delegate;
        address delegatee_delegate;

        // ====== Requirements for this method ======

        // Require account is not delegatee of sender
        address delegateeOfSenderBefore_delegate = getPropositionDelegate(e_delegate.msg.sender);
        require delegateeOfSenderBefore_delegate != account;

        // Require account is not the delegatee
        require delegatee_delegate != account;

        // Require account does not call delegate methods
        require e_delegate.msg.sender != account;

         // ====== Method ======
        delegate(e_delegate, delegatee_delegate);

    } else if (f.selector == delegateByType(address, uint8).selector) {

        // ===== Variables for this method ======
        env e_delegateByType;
        address delegatee_delegateByType;

        // ====== Requirements for this method ======

        // Require account is not delegatee of sender
        address delegateeOfSenderBefore_delegateByType = getPropositionDelegate(e_delegateByType.msg.sender);
        require delegateeOfSenderBefore_delegateByType != account;

        // Require account is not the delegatee
        require delegatee_delegateByType != account;

        // Require account does not call delegate methods
        require e_delegateByType.msg.sender != account;

        // ====== Method ======
        delegateByType(e_delegateByType, delegatee_delegateByType, PROPOSITION_POWER());

    } else if (f.selector == metaDelegate(address, address, uint256, uint8, bytes32, bytes32).selector) {

        // ===== Variables for this method ======
        env e_metaDelegate;
        address delegatee_metaDelegate;
        address delegator_metaDelegate;
        uint256 deadline_metaDelegate;
        uint8 v_metaDelegate;
        bytes32 r_metaDelegate;
        bytes32 s_metaDelegate;

        // ====== Requirements for this method ======

        // Require account is not the delegatee
        require delegatee_metaDelegate != account;

        // Require account is not the delegator 
        require delegator_metaDelegate != account;

        // Require account is not delegatee of the delegator
        address delegateeOfDelegatorBefore_metaDelegate = getPropositionDelegate(delegator_metaDelegate);
        require delegateeOfDelegatorBefore_metaDelegate != account;

        // ====== Method ======
        metaDelegate(e_metaDelegate, delegator_metaDelegate, delegatee_metaDelegate,deadline_metaDelegate,v_metaDelegate,r_metaDelegate,s_metaDelegate);
    
    } else if (f.selector == metaDelegateByType(address, address, uint8, uint256, uint8, bytes32, bytes32).selector) {
        
        // ===== Variables for this method ======
        env e_metaDelegateByType;
        address delegatee_metaDelegateByType;
        address delegator_metaDelegateByType;
        uint256 deadline_metaDelegateByType;
        uint8 v_metaDelegateByType;
        bytes32 r_metaDelegateByType;
        bytes32 s_metaDelegateByType;

        // ====== Requirements for this method ======

        // Require account is not the delegatee
        require delegatee_metaDelegateByType != account;

        // Require account is not the delegator 
        require delegator_metaDelegateByType != account;

        // Require account is not delegatee of the delegator
        address delegateeOfDelegatorBefore_metaDelegateByType = getPropositionDelegate(delegator_metaDelegateByType);
        require delegateeOfDelegatorBefore_metaDelegateByType != account;
        
        // ====== Method ======
        metaDelegateByType(e_metaDelegateByType, delegator_metaDelegateByType, delegatee_metaDelegateByType, PROPOSITION_POWER(), deadline_metaDelegateByType, v_metaDelegateByType, r_metaDelegateByType, s_metaDelegateByType);

    } else if (f.selector == _governancePowerTransferByType(uint104, uint104, address, uint8).selector) {

         // ===== Variables for this method ======
        env e_governancePowerTransferByType;
        address delegatee_governancePowerTransferByType;
        uint104 impactOnDelegationBefore;
        uint104 impactOnDelegationAfter;

        // ====== Requirements for this method ======

        // Require account is not the delegatee
        require delegatee_governancePowerTransferByType != account;

        // ====== Method ======
        _governancePowerTransferByType(e_governancePowerTransferByType, impactOnDelegationBefore, impactOnDelegationBefore, delegatee_governancePowerTransferByType, PROPOSITION_POWER());

    } else if (f.selector == transfer(address, uint256).selector) {

        // ===== Variables for this method ======
        env e_transfer;
        address to_transfer;
        uint256 amount_transfer;

        // ====== Requirements for this method ======

        // Require account is not the delegatee of the sender
        address delegateeOfSenderBefore_transfer = getPropositionDelegate(e_transfer.msg.sender);
        require delegateeOfSenderBefore_transfer != account;

        // Require account is not delegatee of "to" account
        address propositionDelegatee_transfer = getPropositionDelegate(to_transfer);
        require propositionDelegatee_transfer != account;

        // ====== Method ======
        transfer(e_transfer, to_transfer, amount_transfer);

    } else if (f.selector == transferFrom(address, address, uint256).selector) {
        // ===== Variables for this method ======
        env e_transferFrom;
        address to_transferFrom;
        address from_transferFrom;
        uint256 amount_transferFrom;

        // ====== Requirements for this method ======

        // Require account is not the delegatee of the sender
        address delegateeOfSenderBefore_transferFrom = getPropositionDelegate(e_transferFrom.msg.sender);
        require delegateeOfSenderBefore_transferFrom != account;

        // Require account is not delegatee of "to" account
        address propositionDelegatee_transferFrom = getPropositionDelegate(to_transferFrom);
        require propositionDelegatee_transferFrom  != account;

        // ====== Method ======
        transferFrom(e_transferFrom, from_transferFrom, to_transferFrom, amount_transferFrom);
    }

    else {
        // ====== Run all other methods ======
        f(e, args);
    }

    uint256 accountPowerAfter = getPowerCurrent(account, PROPOSITION_POWER());
    uint256 accountBalanceAfter = balanceOf(account);

    assert accountPowerAfter == accountBalanceAfter, "Power of account must be equal to its AAVE Balance when account is not delegating nor being delegated to";
}

/**

    RULE 3

    Condition: Account1 and Account2 are not delegating
    Checks: VOTING_POWER
    Checks Methods: Transfer
    Outcome: PASSES

    Transfering tokens of amount z >= 0 from account1 to account2 should: 
    - Decrease voting power of account1 by z 
    - Increase power of account2 by z

*/
rule transferChangesVotingPowerWhenAccount1AndAccount2NotDelegating(address account1, address account2, uint256 amount) {
    env e;

    require account1 != account2;

    uint256 account1VotingPowerBefore = getPowerCurrent(account1, VOTING_POWER());
    uint256 account2VotingPowerBefore = getPowerCurrent(account2, VOTING_POWER());

    uint8 account1DelegationState = getDelegationState(account1);
    uint8 account2DelegationState = getDelegationState(account2);

    require e.msg.sender == account1;
    require account1DelegationState == NO_DELEGATION();
    require account2DelegationState == NO_DELEGATION();

    transfer(e,account2,amount);

    uint256 account1VotingPowerAfter = getPowerCurrent(account1, VOTING_POWER());
    uint256 account2VotingPowerAfter = getPowerCurrent(account2, VOTING_POWER()); 

    assert account1VotingPowerAfter == account1VotingPowerBefore - amount, "Account voting power must decrease when account transfers to when account is not delegating power";
    assert account2VotingPowerAfter == account2VotingPowerBefore + amount, "Account voting power must increase when account receives transfer when account is not delegating power";
}

/**

    RULE 4

    Condition: Account1 and Account2 are not delegating
    Checks: PROPOSITION_POWER
    Checks Methods: Transfer
    Outcome: PASSES

    Transfering tokens of amount z >= 0 from account1 to account2 should:
    - Decrease proposition power of account1 by z
    - Increase power of account2 by z 

*/
rule transferChangesPropositionPowerWhenAccount1AndAccount2NotDelegating(address account1, address account2, uint256 amount) {
    env e;

    require account1 != account2;

    uint256 account1PropositionPowerBefore = getPowerCurrent(account1, PROPOSITION_POWER());
    uint256 account2PropositionPowerBefore = getPowerCurrent(account2, PROPOSITION_POWER());

    uint8 account1DelegationState = getDelegationState(account1);
    uint8 account2DelegationState = getDelegationState(account2);

    require e.msg.sender == account1;
    require account1DelegationState == NO_DELEGATION();
    require account2DelegationState == NO_DELEGATION();

    transfer(e,account2,amount);

    uint256 account1PropositionPowerAfter = getPowerCurrent(account1, PROPOSITION_POWER());
    uint256 account2PropositionPowerAfter= getPowerCurrent(account2, PROPOSITION_POWER());  

    assert account1PropositionPowerAfter == account1PropositionPowerBefore - amount, "Proposition voting power must decrease when account transfers to when account is not delegating power";
    assert account2PropositionPowerAfter == account2PropositionPowerBefore + amount, "Proposition voting power must increase when account receives transfer when account is not delegating power";
}

/**

    RULE 5

    Condition: Account 1 and account 2 are not delegating
    Checks: VOTING_POWER
    Checks Methods: Delegate, getVotingDelegate (i.e. _votingDelegateeV2 map is updated)
    Outcome: PASSES

    Delegating from account1 to account2 should:
    - Increase account2's power by account1's balance

*/
rule delegatingChangesVotingPowerWhenAccount1AndAccount2NotDelegating(address account1, address account2) {
    env e;

    // require the accounts are not the same
    require account1 != account2;

    // require account 2 is not the 0 address
    require account2 != 0;

    // require account1 is delegating
    require e.msg.sender == account1;

    // Get Voting Power before for both accounts
    uint256 account1VotingPowerBefore = getPowerCurrent(account1, VOTING_POWER());
    uint256 account2VotingPowerBefore = getPowerCurrent(account2, VOTING_POWER());

    // Require Account 1 and Account 2 are not delegating
    uint8 account1DelegationState = getDelegationState(account1);
    uint8 account2DelegationState = getDelegationState(account2);

    require account1DelegationState == NO_DELEGATION();
    require account2DelegationState == NO_DELEGATION();

    delegate(e,account2);

    uint256 account1VotingPowerAfter = getPowerCurrent(account1, VOTING_POWER());
    uint256 account2VotingPowerAfter = getPowerCurrent(account2, VOTING_POWER()); 

    uint256 account1Balance = balanceOf(account1);

    address delegatee = getVotingDelegate(account1);

    assert account1VotingPowerAfter == (account1VotingPowerBefore - account1Balance), "Account voting power must decrease by balance amount when account delegates power";
    assert account2VotingPowerAfter == (account2VotingPowerBefore + account1Balance), "Account voting power must increase by balance amount when account has been delegated power to";
    assert delegatee == account2, "Delegatee must be account 2";
}

/**

    RULE 6

    Condition: Account 1 and account 2 are not delegating
    Checks: PROPOSITION_POWER
    Checks Methods: Delegate, getPropositionDelegate (i.e. _propositionDelegateeV2 map is updated)
    Outcome: PASSES

    Delegating from account1 to account2 should:
    - Increase account2's power by account1's balance

*/
rule delegatingChangesPropositionPowerWhenAccount1AndAccount2NotDelegating(address account1, address account2) {
    env e;

    // require the accounts are not the same
    require account1 != account2;

    // require account 2 is not the 0 address
    require account2 != 0;

    // require account1 is delegating
    require e.msg.sender == account1;

    // Get Proposition Power before for both accounts
    uint256 account1PropositionPowerBefore = getPowerCurrent(account1, PROPOSITION_POWER());
    uint256 account2PropositionPowerBefore = getPowerCurrent(account2, VOTING_POWER());

    // Require Account 1 and Account 2 are not delegating
    uint8 account1DelegationState = getDelegationState(account1);
    uint8 account2DelegationState = getDelegationState(account2);

    require account1DelegationState == NO_DELEGATION();
    require account2DelegationState == NO_DELEGATION();

    delegate(e,account2);

    uint256 account1PropositionPowerAfter = getPowerCurrent(account1, PROPOSITION_POWER());
    uint256 account2PropositionPowerAfter = getPowerCurrent(account2, PROPOSITION_POWER()); 

    uint256 account1Balance = balanceOf(account1);

    address delegatee = getPropositionDelegate(account1);

    assert account1PropositionPowerAfter == (account1PropositionPowerBefore - account1Balance), "Account Proposition power must decrease by balance amount when account delegates power";
    assert account2PropositionPowerAfter == (account2PropositionPowerBefore + account1Balance), "Account Proposition power must increase by balance amount when account has been delegated power to";
    assert delegatee == account2, "Delegatee must be account 2";
}

/**

    RULE 7

    Condition: Account1 is delegating power to delegatee1, account2 is not delegating power to anybody
    Checks: VOTING_POWER
    Checks methods: Transfer
    Outcome: PASSES

    Transfering tokens of amount z >= 0 from account1 to account2 should:
    - Keep the voting power of account1 the same 
    - Decrease delegatee1's voting power by z
    - Increase account2's voting power by z
*/
rule transferChangesAccount2VotingPowerWhenAccount1DelegatesAndAccount2DoesNotDelegate(address account1, address account2, uint256 amount) {
    env e;
    address delegatee1;

    // require the accounts are not the same
    require account1 != account2;

    // Require that account1 is delegating power to delegatee1
    require delegatee1 == getVotingDelegate(account1);

    // Require that the account is not delegating to nobody (i.e. itself or zero account)
    require delegatee1 != account1;
    require delegatee1 != 0;

    uint8 account1DelegationState = getDelegationState(account1);
    require account1DelegationState == VOTING_DELEGATED();

    // Require account 2 is not delegating
    uint8 account2DelegationState = getDelegationState(account2);
    require account2DelegationState == NO_DELEGATION();

    // Get Voting Power before for all accounts
    uint256 account1VotingPowerBefore = getPowerCurrent(account1, VOTING_POWER());
    uint256 delegatee1VotingPowerBefore = getPowerCurrent(delegatee1, VOTING_POWER());
    uint256 account2VotingPowerBefore = getPowerCurrent(account2, VOTING_POWER());

    // require account1 sends the transfer
    require e.msg.sender == account1;
    transfer(e,account2,amount);
    
    uint256 account1VotingPowerAfter = getPowerCurrent(account1, VOTING_POWER());
    uint256 delegatee1VotingPowerAfter = getPowerCurrent(delegatee1, VOTING_POWER());
    uint256 account2VotingPowerAfter = getPowerCurrent(account2, VOTING_POWER()); 

    assert account1VotingPowerAfter == account1VotingPowerBefore, "account1 voting power after must not change after transfer because it was delegating";
    assert delegatee1 != account2 => account2VotingPowerAfter == account2VotingPowerBefore + amount, "account2's power must increase by amount of transfer";    
}


/**

    RULE 8

    Condition: Account1 is delegating power to delegatee1, account2 is not delegating power to anybody
    Checks: PROPOSITION_POWER
    Checks methods: Transfer
    Outcome: PASSES

    Transfering tokens of amount z >= 0 from account1 to account2 should:
    - Keep the proposition power of account1 the same
    - Decrease delegatee1's proposition power by z 
    - Increase account2's proposition power by z
*/
rule transferChangesAccount2PropositionPowerWhenAccount1DelegatesAndAccount2DoesNotDelegate(address account1, address account2, uint256 amount) {
    env e;
    address delegatee1;

    // require the accounts are not the same
    require account1 != account2;

    // Require that account1 is delegating power to delegatee1
    //address propositionDelegatee = getPropositionDelegate(account1);
    //require propositionDelegatee == delegatee1;
    require delegatee1 == getPropositionDelegate(account1);

    // Require that the account is not delegating to nobody (i.e. itself or zero account)
    require delegatee1 != account1;
    require delegatee1 != 0;

    uint8 account1DelegationState = getDelegationState(account1);
    require account1DelegationState == PROPOSITION_DELEGATED();

    // Require account 2 is not delegating
    uint8 account2DelegationState = getDelegationState(account2);
    require account2DelegationState == NO_DELEGATION();

    // Get Proposition Power before for all accounts
    uint256 account1PropositionPowerBefore = getPowerCurrent(account1, PROPOSITION_POWER());
    uint256 delegatee1PropositionPowerBefore = getPowerCurrent(delegatee1, PROPOSITION_POWER());
    uint256 account2PropositionPowerBefore = getPowerCurrent(account2, PROPOSITION_POWER());

    // require account1 sends the transfer
    require e.msg.sender == account1;
    transfer(e,account2,amount);
    
    uint256 account1PropositionPowerAfter = getPowerCurrent(account1, PROPOSITION_POWER());
    uint256 delegatee1PropositionPowerAfter = getPowerCurrent(delegatee1, PROPOSITION_POWER());
    uint256 account2PropositionPowerAfter = getPowerCurrent(account2, PROPOSITION_POWER()); 

    assert account1PropositionPowerAfter == account1PropositionPowerBefore, "account1 Proposition power after must not change after transfer because it was delegating";
    assert delegatee1 != account2 => account2PropositionPowerAfter == account2PropositionPowerBefore + amount, "account2's power must increase by amount of transfer";    
}

/**

    RULE 9

    Condition: Account1 is delegating power to delegatee1, account2 is not delegating power to anybody
    Checks: VOTING_POWER
    Checks methods: Transfer
    Outcome: PASSES

    Note: FAILS without normalization. Also note this is the same as Rule 7, except for the assertion at the end. 
    This Rule has been separated from Rule 7 to highlight a potential bug in the contract.

    If assert is: delegatee1 != account2 => delegatee1VotingPowerAfter == delegatee1VotingPowerBefore - normalize(amount);
    then it fails. Example: https://prover.certora.com/output/69969/c2a94289c9fe0519f945?anonymousKey=93eac460219cd217c40f1dab936a240922020f8d
    In this example, the difference between the delegatee1VotingPowerBefore and delegatee1VotingPowerAfter is twice the amount of the amount transferred.

    Transfering tokens of amount z >= 0 from account1 to account2 should:
    - Keep the voting power of account1 the same (i.e. zero)
    - Decrease delegatee1's voting power by z
    - Increase account2's voting power by z
*/
rule transferChangesDelegateeVotingPowerWhenAccount1DelegatesAndAccount2DoesNotDelegate(address account1, address account2, uint256 amount) {
    env e;
    address delegatee1;

    // require the accounts are not the same
    require account1 != account2;

    // Require that account1 is delegating power to delegatee1
    require delegatee1 == getVotingDelegate(account1);

    // Require that the account is not delegating to nobody (i.e. itself or zero account)
    require delegatee1 != account1;
    require delegatee1 != 0;

    uint8 account1DelegationState = getDelegationState(account1);
    require account1DelegationState == VOTING_DELEGATED();

    // Account1 Balance before
    uint256 account1BalanceBefore = balanceOf(account1); // remove

    uint72 delegateeVotingBalanceBefore = getDelegatedVotingBalance(delegatee1); // remove
    address delegateeVotingDelegatee = getVotingDelegate(delegatee1); // added for finding bug
    uint8 delegateeDelegationState = getDelegationState(delegatee1);

    // Require account 2 is not delegating
    uint8 account2DelegationState = getDelegationState(account2);
    require account2DelegationState == NO_DELEGATION();

    // Get Voting Power before for all accounts
    uint256 account1VotingPowerBefore = getPowerCurrent(account1, VOTING_POWER());
    uint256 delegatee1VotingPowerBefore = getPowerCurrent(delegatee1, VOTING_POWER());
    uint256 account2VotingPowerBefore = getPowerCurrent(account2, VOTING_POWER());

    // require account1 sends the transfer
    require e.msg.sender == account1;
    transfer(e,account2,amount);
    
    uint256 account1VotingPowerAfter = getPowerCurrent(account1, VOTING_POWER());
    uint256 delegatee1VotingPowerAfter = getPowerCurrent(delegatee1, VOTING_POWER());
    uint256 account2VotingPowerAfter = getPowerCurrent(account2, VOTING_POWER()); 

    // Account1 Balance after
    uint256 account1BalanceAfter = balanceOf(account1); //remove

    uint72 delegateeVotingBalanceAfter = getDelegatedVotingBalance(delegatee1); // remove
    uint256 normalizedAmount = normalize(amount); //remove

    assert account1VotingPowerAfter == account1VotingPowerBefore, "account1 voting power after must not change after transfer because it was delegating";
    assert delegatee1 != account2 => delegatee1VotingPowerAfter == delegatee1VotingPowerBefore - normalize(account1BalanceBefore) + normalize(account1BalanceAfter), "delegatee's power must decrease by amount of transfer";
}

/**

    RULE 10

    Condition: Account1 is delegating power to delegatee1, account2 is not delegating power to anybody
    Checks: PROPOSITION_POWER
    Checks methods: Transfer
    Outcome: PASSES

    Note: FAILS without normalization. Also note this is the same as rule 8, except for the assertion at the end. 
    This Rule has been separated from Rule 8 to highlight a potential bug in the contract.

    Transfering tokens of amount z >= 0 from account1 to account2 should:
    - Keep the proposition power of account1 the same (i.e. zero)
    - Decrease delegatee1's proposition power by z
    - Increase account2's proposition power by z
*/
rule transferChangesDelegateePropositionPowerWhenAccount1DelegatesAndAccount2DoesNotDelegate(address account1, address account2, uint256 amount) {
    env e;
    address delegatee1;

    // require the accounts are not the same
    require account1 != account2;

    // Require that account1 is delegating power to delegatee1
    require delegatee1 == getPropositionDelegate(account1);

    // Require that the account is not delegating to nobody (i.e. itself or zero account)
    require delegatee1 != account1;
    require delegatee1 != 0;

    uint8 account1DelegationState = getDelegationState(account1);
    require account1DelegationState == PROPOSITION_DELEGATED();

    // Account1 Balance before
    uint256 account1BalanceBefore = balanceOf(account1); // remove

    uint72 delegateePropositionBalanceBefore = getDelegatedPropositionBalance(delegatee1); // remove
    address delegateePropositionDelegatee = getPropositionDelegate(delegatee1); // added for finding bug
    uint8 delegateeDelegationState = getDelegationState(delegatee1);

    // Require account 2 is not delegating
    uint8 account2DelegationState = getDelegationState(account2);
    require account2DelegationState == NO_DELEGATION();

    // Get Proposition Power before for all accounts
    uint256 account1PropositionPowerBefore = getPowerCurrent(account1, PROPOSITION_POWER());
    uint256 delegatee1PropositionPowerBefore = getPowerCurrent(delegatee1, PROPOSITION_POWER());
    uint256 account2PropositionPowerBefore = getPowerCurrent(account2, PROPOSITION_POWER());

    // require account1 sends the transfer
    require e.msg.sender == account1;
    transfer(e,account2,amount);
    
    uint256 account1PropositionPowerAfter = getPowerCurrent(account1, PROPOSITION_POWER());
    uint256 delegatee1PropositionPowerAfter = getPowerCurrent(delegatee1, PROPOSITION_POWER());
    uint256 account2PropositionPowerAfter = getPowerCurrent(account2, PROPOSITION_POWER()); 

    // Account1 Balance after
    uint256 account1BalanceAfter = balanceOf(account1); //remove

    uint72 delegateePropositionBalanceAfter = getDelegatedPropositionBalance(delegatee1); // remove
    uint256 normalizedAmount = normalize(amount); //remove

    assert account1PropositionPowerAfter == account1PropositionPowerBefore, "account1 Proposition power after must not change after transfer because it was delegating";
    assert delegatee1 != account2 => delegatee1PropositionPowerAfter == delegatee1PropositionPowerBefore - normalize(account1BalanceBefore) + normalize(account1BalanceAfter), "delegatee's power must decrease by amount of transfer";
}

/**

    RULE 11

    Condition: Account1 is delegating power to delegatee1, account2 is not delegating power to anybody
    Checks: VOTING_POWER
    Checks methods: Delegate
    Outcome: PASSES

    Account1 stops delegating its power to delegee1
*/
rule stopDelegatingVotingPower(address account1) {
    env e;
    address delegatee1;

    // Require that account1 is delegating power to delegatee1
    require delegatee1 == getVotingDelegate(account1);

    // Require that the account is not delegating to nobody (i.e. itself or zero account)
    require delegatee1 != account1;
    require delegatee1 != 0;

    uint8 account1DelegationState = getDelegationState(account1);
    require account1DelegationState == VOTING_DELEGATED();

    // Account1 Balance before
    uint256 account1BalanceBefore = balanceOf(account1); 

    // Get Voting Power before for all accounts
    uint256 account1VotingPowerBefore = getPowerCurrent(account1, VOTING_POWER());
    uint256 delegatee1VotingPowerBefore = getPowerCurrent(delegatee1, VOTING_POWER());

    // require account1 sends the transfer
    require e.msg.sender == account1;
    delegate(e,account1);
    
    uint256 account1VotingPowerAfter = getPowerCurrent(account1, VOTING_POWER());
    uint256 delegatee1VotingPowerAfter = getPowerCurrent(delegatee1, VOTING_POWER());

    // Account1 Balance after
    uint256 account1BalanceAfter = balanceOf(account1); 

    assert account1VotingPowerAfter == account1VotingPowerBefore + account1BalanceAfter, "Account1's power must be increased by its balance";
    assert delegatee1VotingPowerAfter == delegatee1VotingPowerBefore - normalize(account1BalanceBefore), "Delegatee's power must be decreased by account1's balance";
}

/**

    RULE 12

    Condition: Account1 is delegating power to delegatee1, account2 is not delegating power to anybody
    Checks: PROPOSITION_POWER
    Checks methods: Delegate
    Outcome: PASSES

    Account1 stops delegating its power to delegee1
*/
rule stopDelegatingPropositionPower(address account1) {
    env e;
    address delegatee1;

    // Require that account1 is delegating power to delegatee1
    require delegatee1 == getPropositionDelegate(account1);

    // Require that the account is not delegating to nobody (i.e. itself or zero account)
    require delegatee1 != account1;
    require delegatee1 != 0;

    uint8 account1DelegationState = getDelegationState(account1);
    require account1DelegationState == PROPOSITION_DELEGATED();

    // Account1 Balance before
    uint256 account1BalanceBefore = balanceOf(account1); 

    // Get Proposition Power before for all accounts
    uint256 account1PropositionPowerBefore = getPowerCurrent(account1, PROPOSITION_POWER());
    uint256 delegatee1PropositionPowerBefore = getPowerCurrent(delegatee1, PROPOSITION_POWER());

    // require account1 sends the transfer
    require e.msg.sender == account1;
    delegate(e,account1);
    
    uint256 account1PropositionPowerAfter = getPowerCurrent(account1, PROPOSITION_POWER());
    uint256 delegatee1PropositionPowerAfter = getPowerCurrent(delegatee1, PROPOSITION_POWER());

    // Account1 Balance after
    uint256 account1BalanceAfter = balanceOf(account1); 

    assert account1PropositionPowerAfter == account1PropositionPowerBefore + account1BalanceAfter, "Account1's power must be increased by its balance";
    assert delegatee1PropositionPowerAfter == delegatee1PropositionPowerBefore - normalize(account1BalanceBefore), "Delegatee's power must be decreased by account1's balance";
}

/**

    RULE 13

    Condition: Account1 is delegating power to delegatee1, account2 is not delegating power to anybody
    Checks: VOTING_POWER
    Checks methods: Delegate, (i.e. _votingDelegateeV2 map is updated)
    Outcome: PASSES

    Account1 transfers delegation to delegatee2
*/
rule transferDelegatingVotingPower(address account1) {
    env e;
    address delegatee1;
    address delegatee2;

    // Require that account1 is delegating power to delegatee1
    require delegatee1 == getVotingDelegate(account1);

    // Require that the account is not delegating to nobody (i.e. itself or zero account)
    require delegatee1 != account1;
    require delegatee1 != 0;
    require delegatee2 != account1;
    require delegatee2 != 0;

    // require delegatee changes
    require delegatee2 != delegatee1;

    uint8 account1DelegationState = getDelegationState(account1);
    require account1DelegationState == VOTING_DELEGATED();

    // Account1 Balance before
    uint256 account1BalanceBefore = balanceOf(account1); // remove

    // Get Voting Power before for all accounts
    uint256 account1VotingPowerBefore = getPowerCurrent(account1, VOTING_POWER());
    uint256 delegatee1VotingPowerBefore = getPowerCurrent(delegatee1, VOTING_POWER());
    uint256 delegatee2VotingPowerBefore = getPowerCurrent(delegatee2, VOTING_POWER());

    // require account1 sends the transfer
    require e.msg.sender == account1;
    delegate(e,delegatee2);
    
    uint256 account1VotingPowerAfter = getPowerCurrent(account1, VOTING_POWER());
    uint256 delegatee1VotingPowerAfter = getPowerCurrent(delegatee1, VOTING_POWER());
    uint256 delegatee2VotingPowerAfter = getPowerCurrent(delegatee2, VOTING_POWER());

    // Account1 Balance after
    uint256 account1BalanceAfter = balanceOf(account1);

    // Retrieve the new delegate of account1
    address newDelegatee = getVotingDelegate(account1);

    assert account1VotingPowerAfter == account1VotingPowerBefore, "Account1's power must not change";
    assert delegatee1VotingPowerAfter == delegatee1VotingPowerBefore - normalize(account1BalanceAfter), "Delegatee's power must decrease by Account1's balance";
    assert delegatee2VotingPowerAfter == delegatee2VotingPowerBefore + normalize(account1BalanceAfter), "Delegatee's power must decrease by Account1's balance";
    assert newDelegatee == delegatee2, "delegatee2 should be the new delegatee of account1";
}

/**

    RULE 14

    Condition: Account1 is delegating power to delegatee1, account2 is not delegating power to anybody
    Checks: PROPOSITION_POWER
    Checks methods: Delegate, (i.e. _propositionDelegateeV2 map is updated)
    Outcome: PASSES

    Account1 transfers delegation to delegatee2
*/
rule transferDelegatingPropositionPower(address account1) {
    env e;
    address delegatee1;
    address delegatee2;

    // Require that account1 is delegating power to delegatee1
    require delegatee1 == getPropositionDelegate(account1);

    // Require that the account is not delegating to nobody (i.e. itself or zero account)
    require delegatee1 != account1;
    require delegatee1 != 0;
    require delegatee2 != account1;
    require delegatee2 != 0;

    // require delegatee changes
    require delegatee2 != delegatee1;

    uint8 account1DelegationState = getDelegationState(account1);
    require account1DelegationState == PROPOSITION_DELEGATED();

    // Account1 Balance before
    uint256 account1BalanceBefore = balanceOf(account1); // remove

    // Get Proposition Power before for all accounts
    uint256 account1PropositionPowerBefore = getPowerCurrent(account1, PROPOSITION_POWER());
    uint256 delegatee1PropositionPowerBefore = getPowerCurrent(delegatee1, PROPOSITION_POWER());
    uint256 delegatee2PropositionPowerBefore = getPowerCurrent(delegatee2, PROPOSITION_POWER());

    // require account1 sends the transfer
    require e.msg.sender == account1;
    delegate(e,delegatee2);
    
    uint256 account1PropositionPowerAfter = getPowerCurrent(account1, PROPOSITION_POWER());
    uint256 delegatee1PropositionPowerAfter = getPowerCurrent(delegatee1, PROPOSITION_POWER());
    uint256 delegatee2PropositionPowerAfter = getPowerCurrent(delegatee2, PROPOSITION_POWER());

    // Account1 Balance after
    uint256 account1BalanceAfter = balanceOf(account1);

    // Retrieve the new delegate of account1
    address newDelegatee = getPropositionDelegate(account1);

    assert account1PropositionPowerAfter == account1PropositionPowerBefore, "Account1's power must not change";
    assert delegatee1PropositionPowerAfter == delegatee1PropositionPowerBefore - normalize(account1BalanceAfter), "Delegatee's power must decrease by Account1's balance";
    assert delegatee2PropositionPowerAfter == delegatee2PropositionPowerBefore + normalize(account1BalanceAfter), "Delegatee's power must decrease by Account1's balance";
    assert newDelegatee == delegatee2, "delegatee2 should be the new delegatee of account1";
}

/**

    RULE 15

    Condition: Account1 is not delegating power to anybody, account2 is delegating power to delegatee2
    Checks: VOTING_POWER
    Checks methods: Transfer
    Outcome: PASSES

    Transfering tokens of amount z >= 0 from account1 to account2 should:
    - Reduce the voting power of account1
    - Keep the voting power of account2 the same
    - Increase the voting power of delegatee2
*/
rule transferChangesVotingPowerA1NotDelegatingA2Delegating(address account1, address account2, uint256 amount) {
    env e;
    address delegatee2;

    // require the accounts are not the same
    require account1 != account2;

    // Require that the account is not delegating to nobody (i.e. itself or zero account)
    require delegatee2 != account2;
    require delegatee2 != 0;

    // Require account1 is not delegating
    uint8 account1DelegationState = getDelegationState(account1);
    require account1DelegationState == NO_DELEGATION();

    // Account2 Balance before
    uint256 account2BalanceBefore = balanceOf(account2);

    // Require account2 is delegating to delegatee2
    uint8 account2DelegationState = getDelegationState(account2);
    require account2DelegationState == VOTING_DELEGATED();
    require delegatee2 == getVotingDelegate(account2);

    // Get Voting Power before for all accounts
    uint256 account1VotingPowerBefore = getPowerCurrent(account1, VOTING_POWER());
    uint256 delegatee2VotingPowerBefore = getPowerCurrent(delegatee2, VOTING_POWER());
    uint256 account2VotingPowerBefore = getPowerCurrent(account2, VOTING_POWER());

    // require account1 sends the transfer
    require e.msg.sender == account1;
    transfer(e,account2,amount);
    
    uint256 account1VotingPowerAfter = getPowerCurrent(account1, VOTING_POWER());
    uint256 delegatee2VotingPowerAfter = getPowerCurrent(delegatee2, VOTING_POWER());
    uint256 account2VotingPowerAfter = getPowerCurrent(account2, VOTING_POWER()); 

    // Account2 Balance after
    uint256 account2BalanceAfter = balanceOf(account2);

    assert account2VotingPowerAfter == account2VotingPowerBefore, "account2 Voting power after must not change after transfer because it was delegating";
    assert account1 != delegatee2 => account1VotingPowerAfter == account1VotingPowerBefore - amount, "account1's Voting power must decrease after transfer";
    assert account1 != delegatee2 => delegatee2VotingPowerAfter == delegatee2VotingPowerBefore - normalize(account2BalanceBefore) + normalize(account2BalanceAfter), "delegatee's power must increase by amount of transfer";
}

/**

    RULE 16

    Condition: Account1 is not delegating power to anybody, account2 is delegating power to delegatee2
    Checks: PROPOSITION_POWER
    Checks methods: Transfer
    Outcome: PASSES

    Transfering tokens of amount z >= 0 from account1 to account2 should:
    - Reduce the proposition power of account1
    - Keep the proposition power of account2 the same
    - Increase the proposition power of delegatee2
*/
rule transferChangesPropositionPowerA1NotDelegatingA2Delegating(address account1, address account2, uint256 amount) {
    env e;
    address delegatee2;

    // require the accounts are not the same
    require account1 != account2;

    // Require that the account is not delegating to nobody (i.e. itself or zero account)
    require delegatee2 != account2;
    require delegatee2 != 0;

    // Require account1 is not delegating
    uint8 account1DelegationState = getDelegationState(account1);
    require account1DelegationState == NO_DELEGATION();

    // Account2 Balance before
    uint256 account2BalanceBefore = balanceOf(account2);

    // Require account2 is delegating to delegatee2
    uint8 account2DelegationState = getDelegationState(account2);
    require account2DelegationState == PROPOSITION_DELEGATED();
    require delegatee2 == getPropositionDelegate(account2);

    // Get Proposition Power before for all accounts
    uint256 account1PropositionPowerBefore = getPowerCurrent(account1, PROPOSITION_POWER());
    uint256 delegatee2PropositionPowerBefore = getPowerCurrent(delegatee2, PROPOSITION_POWER());
    uint256 account2PropositionPowerBefore = getPowerCurrent(account2, PROPOSITION_POWER());

    // require account1 sends the transfer
    require e.msg.sender == account1;
    transfer(e,account2,amount);
    
    uint256 account1PropositionPowerAfter = getPowerCurrent(account1, PROPOSITION_POWER());
    uint256 delegatee2PropositionPowerAfter = getPowerCurrent(delegatee2, PROPOSITION_POWER());
    uint256 account2PropositionPowerAfter = getPowerCurrent(account2, PROPOSITION_POWER()); 

    // Account2 Balance after
    uint256 account2BalanceAfter = balanceOf(account2);

    assert account2PropositionPowerAfter == account2PropositionPowerBefore, "account2 Proposition power after must not change after transfer because it was delegating";
    assert account1 != delegatee2 => account1PropositionPowerAfter == account1PropositionPowerBefore - amount, "account1's proposition power must decrease after transfer";
    assert account1 != delegatee2 => delegatee2PropositionPowerAfter == delegatee2PropositionPowerBefore - normalize(account2BalanceBefore) + normalize(account2BalanceAfter), "delegatee's power must increase by amount of transfer";
}

/**

    RULE 17

    Condition: Account1 is delegating power to delegatee1, account2 is delegating power to delegatee2
    Checks: VOTING_POWER
    Checks methods: Transfer
    Outcome: PASSES

    Transfering tokens of amount z >= 0 from account1 to account2 should:
    - Keep the power of account1 the same
    - Keep the power of account2 the same
    - Decrease the power of delegatee1 by z
    - Increase the power of delegatee2 by z
*/
rule transferChangesVotingPowerA1DelegatingA2Delegating(address account1, address account2, uint256 amount) {
    env e;
    address delegatee1;
    address delegatee2;

    // require the accounts and delegatees are not the same
    require account1 != account2;
    require delegatee2 != delegatee2;

    // Require that the account is not delegating to nobody (i.e. itself or zero account)
    require delegatee1 != account1;
    require delegatee1 != 0;
    require delegatee2 != account2;
    require delegatee2 != 0;

    require account1 != delegatee2;
    require account2 != delegatee1;

    // Require account1 is delegating to delegatee1
    uint8 account1DelegationState = getDelegationState(account1);
    require account1DelegationState == VOTING_DELEGATED();
    require delegatee1 == getVotingDelegate(account1);

    // Require account2 is delegating to delegatee2
    uint8 account2DelegationState = getDelegationState(account2);
    require account2DelegationState == VOTING_DELEGATED();
    require delegatee2 == getVotingDelegate(account2);

    // Account balances before
    uint256 account1BalanceBefore = balanceOf(account1);
    uint256 account2BalanceBefore = balanceOf(account2);

    // Get Voting Power before for all accounts
    uint256 delegatee1VotingPowerBefore = getPowerCurrent(delegatee1, VOTING_POWER());
    uint256 account1VotingPowerBefore = getPowerCurrent(account1, VOTING_POWER());
    uint256 delegatee2VotingPowerBefore = getPowerCurrent(delegatee2, VOTING_POWER());
    uint256 account2VotingPowerBefore = getPowerCurrent(account2, VOTING_POWER());

    // require account1 sends the transfer
    require e.msg.sender == account1;
    transfer(e,account2,amount);
    
    uint256 delegatee1VotingPowerAfter = getPowerCurrent(delegatee1, VOTING_POWER());
    uint256 account1VotingPowerAfter = getPowerCurrent(account1, VOTING_POWER());
    uint256 delegatee2VotingPowerAfter = getPowerCurrent(delegatee2, VOTING_POWER());
    uint256 account2VotingPowerAfter = getPowerCurrent(account2, VOTING_POWER()); 

    // Account balances after
    uint256 account1BalanceAfter= balanceOf(account1);
    uint256 account2BalanceAfter = balanceOf(account2);

    assert account1VotingPowerAfter == account1VotingPowerBefore, "account1 Voting power after must not change after transfer because it was delegating";
    assert account2VotingPowerAfter == account2VotingPowerBefore, "account2 Voting power after must not change after transfer because it was delegating";
    assert delegatee1VotingPowerAfter == delegatee1VotingPowerBefore - normalize(account2BalanceBefore) + normalize(account2BalanceAfter), "delegatee's power must decrease by amount of transfer";
    assert delegatee2VotingPowerAfter == delegatee2VotingPowerBefore - normalize(account2BalanceBefore) + normalize(account2BalanceAfter), "delegatee's power must increase by amount of transfer";
}

/**

    RULE 18

    Condition: Account1 is delegating power to delegatee1, account2 is delegating power to delegatee2
    Checks: PROPOSITION_POWER
    Checks methods: Transfer
    Outcome: PASSES

    Transfering tokens of amount z >= 0 from account1 to account2 should:
    - Keep the power of account1 the same
    - Keep the power of account2 the same
    - Decrease the power of delegatee1 by z
    - Increase the power of delegatee2 by z
*/
rule transferChangesPropositionPowerA1DelegatingA2Delegating(address account1, address account2, uint256 amount) {
    env e;
    address delegatee1;
    address delegatee2;

    // require the accounts and delegatees are not the same
    require account1 != account2;
    require delegatee2 != delegatee2;

    // Require that the account is not delegating to nobody (i.e. itself or zero account)
    require delegatee1 != account1;
    require delegatee1 != 0;
    require delegatee2 != account2;
    require delegatee2 != 0;

    require account1 != delegatee2;
    require account2 != delegatee1;

    // Require account1 is delegating to delegatee1
    uint8 account1DelegationState = getDelegationState(account1);
    require account1DelegationState == PROPOSITION_DELEGATED();
    require delegatee1 == getPropositionDelegate(account1);

    // Require account2 is delegating to delegatee2
    uint8 account2DelegationState = getDelegationState(account2);
    require account2DelegationState == VOTING_DELEGATED();
    require delegatee2 == getPropositionDelegate(account2);

    // Account balances before
    uint256 account1BalanceBefore = balanceOf(account1);
    uint256 account2BalanceBefore = balanceOf(account2);

    // Get Proposition Power before for all accounts
    uint256 delegatee1PropositionPowerBefore = getPowerCurrent(delegatee1, PROPOSITION_POWER());
    uint256 account1PropositionPowerBefore = getPowerCurrent(account1, PROPOSITION_POWER());
    uint256 delegatee2PropositionPowerBefore = getPowerCurrent(delegatee2, PROPOSITION_POWER());
    uint256 account2PropositionPowerBefore = getPowerCurrent(account2, PROPOSITION_POWER());

    // require account1 sends the transfer
    require e.msg.sender == account1;
    transfer(e,account2,amount);
    
    uint256 delegatee1PropositionPowerAfter = getPowerCurrent(delegatee1, PROPOSITION_POWER());
    uint256 account1PropositionPowerAfter = getPowerCurrent(account1, PROPOSITION_POWER());
    uint256 delegatee2PropositionPowerAfter = getPowerCurrent(delegatee2, PROPOSITION_POWER());
    uint256 account2PropositionPowerAfter = getPowerCurrent(account2, PROPOSITION_POWER()); 

    // Account balances after
    uint256 account1BalanceAfter= balanceOf(account1);
    uint256 account2BalanceAfter = balanceOf(account2);

    assert account1PropositionPowerAfter == account1PropositionPowerBefore, "account1 Proposition power after must not change after transfer because it was delegating";
    assert account2PropositionPowerAfter == account2PropositionPowerBefore, "account2 Proposition power after must not change after transfer because it was delegating";
    assert delegatee1PropositionPowerAfter == delegatee1PropositionPowerBefore - normalize(account2BalanceBefore) + normalize(account2BalanceAfter), "delegatee's power must decrease by amount of transfer";
    assert delegatee2PropositionPowerAfter == delegatee2PropositionPowerBefore - normalize(account2BalanceBefore) + normalize(account2BalanceAfter), "delegatee's power must increase by amount of transfer";
}

/**

    RULE 19

    Condition: 
    Checks: VOTING_POWER
    Checks methods: DelegateByType
    Outcome: PASSES

    Delegating from account to delegatee should:
    (1) If account was not delegating, decrease account's voting power by its balance
        If account was delegating, voting power should remain the same
    (2) Increase delegatee's voting power by account's balance
    (3) Keep delegatee's proposition power the same (i.e. shall not influence the other power)
    (4) Keep account's proposition power the same (i.e. shall not influence the other power)
    (5) Update delegatee as account's delegatee
*/

rule integrityOfDelegateByTypeVotingPower() {

    address account;
    address delegatee;
    env e;

    // Require that the account is not delegating to nobody (i.e. itself or zero account)
    require delegatee != 0;
    require delegatee != account;

    // Avoid unrealistic delegated balance
    uint256 delegateeDelegatedBalance = getDelegatedVotingBalance(delegatee);
    require(delegateeDelegatedBalance < MAX_DELEGATED_BALANCE());
    
    // Verify that account doesn't already delegate to delegatee
    address delegateBefore = getVotingDelegate(account);
    require delegateBefore != delegatee;

    // Retrieve delegation state before
    uint8 accountDelegationState = getDelegationState(account);

    // Retrieve powers before
    uint256 delegateeVotingPowerBefore = getPowerCurrent(delegatee, VOTING_POWER());
    uint256 delegateePropositionPowerBefore = getPowerCurrent(delegatee, PROPOSITION_POWER());
    uint256 accountVotingPowerBefore = getPowerCurrent(account, VOTING_POWER());
    uint256 accountPropositionPowerBefore = getPowerCurrent(account, PROPOSITION_POWER());

    // Require the account is the sender
    require account == e.msg.sender;

    delegateByType(e, delegatee, VOTING_POWER());

    // Retrieve powers after
    uint256 delegateeVotingPowerAfter = getPowerCurrent(delegatee, VOTING_POWER());
    uint256 delegateePropositionPowerAfter = getPowerCurrent(delegatee, PROPOSITION_POWER());
    uint256 accountVotingPowerAfter = getPowerCurrent(account, VOTING_POWER());
    uint256 accountPropositionPowerAfter = getPowerCurrent(account, PROPOSITION_POWER());

    // Retrieve account balance after
    uint256 accountBalanceAfter = balanceOf(account);

    // (1a): Verify the account's voting power has decreased by its balance if it wasn't delegating its voting power 
    assert (accountDelegationState == NO_DELEGATION() || accountDelegationState == PROPOSITION_DELEGATED()) => accountVotingPowerAfter == accountVotingPowerBefore - accountBalanceAfter, "account's voting power must decrease by its balance amount because it has delegated it";
    // (1b): Verify the account's voting power remains the same if it was delegating
    assert (accountDelegationState == VOTING_DELEGATED() || accountDelegationState == FULL_POWER_DELEGATED()) && delegateBefore != account => accountVotingPowerAfter == accountVotingPowerBefore, "account's voting power must remain the same because it was delegating";

    // (2): Verify the delegatee's voting power has increased by accounts balance
    assert delegateeVotingPowerAfter == delegateeVotingPowerBefore + normalize(accountBalanceAfter), "delegatee's voting power must increase by accounts balance";

    // (3): Verify delegatee's proposition power is the same
    assert delegateePropositionPowerAfter == delegateePropositionPowerBefore, "delegatee's proposition power must not change";

    // (4): Verify account's proposition power is the same
    assert accountPropositionPowerAfter == accountPropositionPowerBefore, "account's proposition power must not change";

    // (5): Verify the accounts voting delegatee is delegatee
    address delegateeAfter = getVotingDelegate(account);
    assert delegateeAfter == delegatee;
}

/**

    RULE 20

    Checks: PROPOSITION_POWER
    Checks methods: DelegateByType
    Outcome: PASSES

    Delegating from account to delegatee should:
    (1) If account was not delegating, decrease account's proposition power by its balance
        If account was delegating, proposition power should remain the same
    (2) Increase delegatee's proposition power by account's balance
    (3) Keep delegatee's voting power the same (i.e. shall not influence the other power)
    (4) Keep account's voting power the same (i.e. shall not influence the other power)
    (5) Update delegatee as account's delegatee
*/

rule integrityOfDelegateByTypePropositionPower() {

    address account;
    address delegatee;
    env e;

    // Require that the account is not delegating to nobody (i.e. itself or zero account)
    require delegatee != 0;
    require delegatee != account;

    // Avoid unrealistic delegated balance
    uint256 delegateeDelegatedBalance = getDelegatedPropositionBalance(delegatee);
    require(delegateeDelegatedBalance < MAX_DELEGATED_BALANCE());
    
    // Verify that account doesn't already delegate to delegatee
    address delegateBefore = getPropositionDelegate(account);
    require delegateBefore != delegatee;

    // Retrieve delegation state before
    uint8 accountDelegationState = getDelegationState(account);

    // Retrieve powers before
    uint256 delegateeVotingPowerBefore = getPowerCurrent(delegatee, VOTING_POWER());
    uint256 delegateePropositionPowerBefore = getPowerCurrent(delegatee, PROPOSITION_POWER());
    uint256 accountVotingPowerBefore = getPowerCurrent(account, VOTING_POWER());
    uint256 accountPropositionPowerBefore = getPowerCurrent(account, PROPOSITION_POWER());

    // Require the account is the sender
    require account == e.msg.sender;

    delegateByType(e, delegatee, PROPOSITION_POWER());

    // Retrieve powers after
    uint256 delegateeVotingPowerAfter = getPowerCurrent(delegatee, VOTING_POWER());
    uint256 delegateePropositionPowerAfter = getPowerCurrent(delegatee, PROPOSITION_POWER());
    uint256 accountVotingPowerAfter = getPowerCurrent(account, VOTING_POWER());
    uint256 accountPropositionPowerAfter = getPowerCurrent(account, PROPOSITION_POWER());

    // Retrieve account balance after
    uint256 accountBalanceAfter = balanceOf(account);

    // (1a): Verify the account's proposition power has decreased by its balance if it wasn't delegating its proposition power 
    assert (accountDelegationState == NO_DELEGATION() || accountDelegationState == VOTING_DELEGATED()) => accountPropositionPowerAfter == accountPropositionPowerBefore - accountBalanceAfter, "account's proposition power must decrease by its balance amount because it has delegated it";
    // (1b): Verify the account's proposition power remains the same if it was delegating
    assert (accountDelegationState == PROPOSITION_DELEGATED() || accountDelegationState == FULL_POWER_DELEGATED()) && delegateBefore != account => accountPropositionPowerAfter == accountPropositionPowerBefore, "account's proposition power must remain the same because it was delegating";

    // (2): Verify the delegatee's proposition power has increased by accounts balance
    assert delegateePropositionPowerAfter == delegateePropositionPowerBefore + normalize(accountBalanceAfter), "delegatee's proposition power must increase by accounts balance";

    // (3): Verify delegatee's proposition power is the same
    assert delegateeVotingPowerAfter == delegateeVotingPowerBefore, "delegatee's voting power must not change";

    // (4): Verify account's voting power is the same
    assert accountVotingPowerAfter == accountVotingPowerBefore, "account's voting power must not change";

    // (5): Verify the accounts proposition delegatee is delegatee
    address delegateeAfter = getPropositionDelegate(account);
    assert delegateeAfter == delegatee;
}

/**

    RULE 21

    Condition: Delegatee is the same as sender or zero address
    Checks: VOTING_POWER
    Checks methods: delegate
    Outcome: FAILS

    Example of failure: https://prover.certora.com/output/69969/8f23a062c12a9ea93a04?anonymousKey=b9f42f92ca45fdb26896cb9e2eb208c9b7542a5c
    VotingPowerBefore = 0
    VotingPowerAfter = 0x5fb2
    But it should be: VotingPowerAfter == VotingPowerBefore
    (Failure probably because of normalization, but ideally maybe this shouldn't happen. This rule could be 'fixed' with normalization, 
    but wanted to leave it as it is to bring attention to it and to verify whether this is the intended behaviour.)

    Delegating from sender to itself or zero address should:
    - Keep sender's delegation the same
*/
rule delegateToNobodyVotingPower() {
    address delegatee;
    env e;
    require delegatee == 0 || delegatee == e.msg.sender;
    uint256 votingPowerBefore = getPowerCurrent(e.msg.sender, VOTING_POWER());
    delegate(e, delegatee);
    uint256 votingPowerAfter = getPowerCurrent(e.msg.sender, VOTING_POWER());
    assert votingPowerAfter == votingPowerBefore, "voting power must not change because sender delegated to nobody";
}

/**

    RULE 22

    Condition: Delegatee is the same as sender or zero address
    Checks: PROPOSITION_POWER
    Checks methods: delegate
    Outcome: FAILS

    Example of failure: https://prover.certora.com/output/69969/f571aa9c04099dd46c60?anonymousKey=c8130403d4b61b8c8b0b36459ee2c8178792f478
    VotingPowerBefore = 0x2540be3fffffffffffdabf41c00
    VotingPowerAfter = 0x2540be400000000000000000000
    But it should be: VotingPowerAfter == VotingPowerBefore
    (Failure probably because of normalization, but ideally maybe this shouldn't happen. This rule could be 'fixed' with normalization, 
    but wanted to leave it as it is to bring attention to it and to verify whether this is the intended behaviour.)

    Delegating from sender to itself or zero address should:
    - Keep sender's delegation the same
*/
rule delegateToNobodyPropositionPower() {
    address delegatee;
    env e;
    require delegatee == 0 || delegatee == e.msg.sender;
    uint256 propositionPowerBefore = getPowerCurrent(e.msg.sender, PROPOSITION_POWER());
    delegate(e, delegatee);
    uint256 propositionPowerAfter= getPowerCurrent(e.msg.sender, PROPOSITION_POWER());
    assert propositionPowerAfter == propositionPowerBefore, "proposition power must not change because sender delegated to nobody";
}

/**

    RULE 23

    Condition: delegatee1 has been delegated to
    Checks: VOTING_POWER
    Checks methods: delegate
    Outcome: FAILS

    Example: https://prover.certora.com/output/69969/99280d183d76908fe797?anonymousKey=160e3a92be63848f8f9b0eb87d2d19e9fc6d999a
    delegatee1VotingPowerBefore = 0xdac7694cfc00
    delegatee1VotingPowerAfter = 0xdac7694cfc00
    delegatee2VotingPowerBefore = 0x530e18293000
    delegatee2VotingPowerBefore =  0x530e18293000
    delegatee1Balance = 0x2540be400

    Balance is greater than 0, but voting powers of delegatee1 and delegatee2 do not change.
    (Failure probably because of normalization, but ideally maybe this shouldn't happen. This rule could be 'fixed' with normalization, 
    but wanted to leave it as it is to bring attention to it and to verify whether this is the intended behaviour.)

    An account can not delegate power that has been delegated to it from another account.

    Delegating someone else's power to another account should:
    - Keep sender's delegation the same
    - Keep receiver's delegation the same
*/

rule cannotDelegateAnothersVotingPower() {

    address delegatee1;
    address delegatee2;
    env e;

    uint72 delegatee1VotingBalance = getDelegatedVotingBalance(delegatee1);
    require delegatee1VotingBalance > 0;

    uint256 delegatee1Balance = balanceOf(delegatee1);

    uint256 delegatee1VotingPowerBefore = getPowerCurrent(delegatee1, VOTING_POWER());
    uint256 delegatee2VotingPowerBefore = getPowerCurrent(delegatee2, VOTING_POWER());
    
    require e.msg.sender == delegatee1;

    delegate(e, delegatee2);

    uint256 delegatee1VotingPowerAfter = getPowerCurrent(delegatee1, VOTING_POWER());
    uint256 delegatee2VotingPowerAfter = getPowerCurrent(delegatee2, VOTING_POWER());

    assert delegatee1Balance == 0 => delegatee1VotingPowerAfter == delegatee1VotingPowerBefore - delegatee1Balance, "voting power must not change";
    assert delegatee1Balance != 0 => delegatee1VotingPowerAfter == delegatee1VotingPowerBefore - normalize(delegatee1Balance), "voting power must not change";
    assert delegatee2VotingPowerAfter == delegatee2VotingPowerBefore + normalize(delegatee1Balance), "voting power must not change";
}

/**

    RULE 24

    Condition: delegatee1 has been delegated to
    Checks: PROPOSITION_POWER
    Checks methods: delegate
    Outcome: FAILS

    Example: https://prover.certora.com/output/69969/99280d183d76908fe797?anonymousKey=160e3a92be63848f8f9b0eb87d2d19e9fc6d999a
    delegatee1VotingPowerBefore = 0x4f24ec303800
    delegatee1VotingPowerAfter = 0x4f27403c1c00
    delegatee2VotingPowerBefore = 0x71d9bd6ed800
    delegatee2VotingPowerBefore =  0x530e18293000
    delegatee1Balance = 0x2540be400

    Balance is greater than 0, but voting power of delegatee2 did not change.
    (Failure probably because of normalization, but ideally maybe this shouldn't happen. This rule could be 'fixed' with normalization, 
    but wanted to leave it as it is to bring attention to it and to verify whether this is the intended behaviour.)

    An account can not delegate power that has been delegated to it from another account.

    Delegating someone else's power to another account should:
    - Keep sender's delegation the same
    - Keep receiver's delegation the same
*/

rule cannotDelegateAnothersPropositionPower() {

    address delegatee1;
    address delegatee2;
    env e;

    uint72 delegatee1PropositionBalance = getDelegatedPropositionBalance(delegatee1);
    require delegatee1PropositionBalance > 0;

    uint256 delegatee1Balance = balanceOf(delegatee1);

    uint256 delegatee1PropositionPowerBefore = getPowerCurrent(delegatee1, PROPOSITION_POWER());
    uint256 delegatee2PropositionPowerBefore = getPowerCurrent(delegatee2, PROPOSITION_POWER());
    
    require e.msg.sender == delegatee1;

    delegate(e, delegatee2);

    uint256 delegatee1PropositionPowerAfter = getPowerCurrent(delegatee1, PROPOSITION_POWER());
    uint256 delegatee2PropositionPowerAfter = getPowerCurrent(delegatee2, PROPOSITION_POWER());

    assert delegatee1Balance == 0 => delegatee1PropositionPowerAfter == delegatee1PropositionPowerBefore - delegatee1Balance, "Proposition power must not change";
    assert delegatee1Balance != 0 => delegatee1PropositionPowerAfter == delegatee1PropositionPowerBefore - normalize(delegatee1Balance), "Proposition power must not change";
    assert delegatee2PropositionPowerAfter == delegatee2PropositionPowerBefore + normalize(delegatee1Balance), "Proposition power must not change";
}

/**

    RULE 25

    Condition: Address zero does not have voting power
    Checks: VOTING_POWER
    Checks methods: All
    Outcome: FAILS

    Example: https://prover.certora.com/output/69969/e8c043c273a2041ba327?anonymousKey=59402179f79c7c2a08d990619cfc50338c81591e
    Fails when delegate and delegateByType call zero address; then the voting power of the zero address increases
    getPowerCurrent after delegate: 0x4d7883a457ff
*/
invariant zeroAddressHasNoVotingPower()
    getPowerCurrent(0,VOTING_POWER()) == 0

/**
    RULE 26

    Condition: Address zero does not have voting power
    Checks: PROPOSITION_POWER
    Checks methods: All
    Outcome: FAILS

    Example: 
    Fails when delegate and delegateByType call zero address; then the proposition power of the zero address increases
*/
invariant zeroAddressHasNoPropositionPower()
    getPowerCurrent(0,PROPOSITION_POWER()) == 0

/**

    RULE 27

    An account's power is its delegated power plus its balance
    Checks: VOTING_POWER
    Outcome: FAILS due to normalization error. 
*/
invariant integrityOfAccountsVotingPower(env e)
    getPowerCurrent(e.msg.sender, VOTING_POWER()) == getDelegatedVotingBalance(e.msg.sender) + normalize(balanceOf(e.msg.sender))

/**

    RULE 28

    An account's power is its delegated power plus its balance
    Checks: PROPOSITION_POWER
    Outcome: FAILS due to normalization error. 
*/
invariant integrityOfAccountsPropositionPower(env e)
    getPowerCurrent(e.msg.sender, PROPOSITION_POWER()) == getDelegatedPropositionBalance(e.msg.sender) + normalize(balanceOf(e.msg.sender))

/**

    RULE 29

    Condition: method is not metaDelegate nor metaDelegateByType
    Checks method: All
    Outcome: PASSES

    The delegatee of an account only changes if they are the sender of a method
*/

rule onlyDelegatorCanChangeDelegatee(method f)
    filtered {
        f -> f.selector != metaDelegate(address, address, uint256, uint8, bytes32, bytes32).selector
            && f.selector != metaDelegateByType(address, address, uint8, uint256, uint8, bytes32, bytes32).selector
    }
    {
        env e;
        address delegatee;
        address account;
        calldataarg args;

        address delegateeBefore = getVotingDelegate(account);
        f(e, args);
        address delegateeAfter = getVotingDelegate(account);

        assert delegateeAfter != delegateeBefore => e.msg.sender == account;
    }

/**

    RULE 30

    Checks method: All

    The balances change only on ERC20 functions, not on delegation functions
*/

rule delegationFunctionsDoNotChangeBalances(){
    env e;
    method f;
    address account;
    calldataarg args;

    uint256 balanceBefore = balanceOf(account);

    f(e, args);

    uint256 balanceAfter = balanceOf(account);

    // Verify delegate functions do not change balance
    assert balanceBefore != balanceAfter =>
        f.selector != delegate(address).selector &&
        f.selector != delegateByType(address,uint8).selector &&
        f.selector != metaDelegate(address,address,uint256,uint8,bytes32,bytes32).selector &&
        f.selector != metaDelegateByType(address,address,uint8,uint256,uint8,bytes32,bytes32).selector;
}

/**

    RULE 31

    Checks: VOTING_POWER
    Checks method: All
    Outcome: PASSES

    An account's voting power is increased only when it:
    - Receives transfer of tokens
    - Receives delegation
    - Delegator receives transfer
*/

rule votingPowerIncreasedOnlyByTransferAndDelegation(){
    env e;
    method f;
    address account;
    calldataarg args;

    uint256 powerBefore = getPowerCurrent(account, VOTING_POWER());

    address to_delegate;
    address to_delegateByType;
    address delegatee_metaDelegate;
    address delegatee_metaDelegateByType;
    address to_transfer;
    address to_transferFrom;
    address delegatee_governancePowerTransferByType;

    if (f.selector == delegate(address).selector) {
        env e_delegate;
        uint256 balance_delegate = balanceOf(e_delegate.msg.sender);
        require balance_delegate > 0;
        require e_delegate.msg.sender != account;
        delegate(e_delegate,to_delegate);
    } else if (f.selector == delegateByType(address,uint8).selector) {
        env e_delegateByType;
        uint256 balance_delegateByType = balanceOf(e_delegateByType.msg.sender);
        require balance_delegateByType > 0;
        require e_delegateByType.msg.sender != account;
        delegateByType(e_delegateByType,to_delegateByType,VOTING_POWER());
    } else if (f.selector == metaDelegate(address,address,uint256,uint8,bytes32,bytes32).selector) {
        env e_metaDelegate;
        address delegator_metaDelegate;
        uint256 deadline_metaDelegate;
        uint8 v_metaDelegate;
        bytes32 r_metaDelegate;
        bytes32 s_metaDelegate;
        uint256 balance_metaDelegate = balanceOf(delegator_metaDelegate);
        require balance_metaDelegate > 0;
        require delegator_metaDelegate != account;
        metaDelegate(e_metaDelegate, delegator_metaDelegate, delegatee_metaDelegate,deadline_metaDelegate,v_metaDelegate,r_metaDelegate,s_metaDelegate);
    } else if (f.selector == metaDelegateByType(address,address,uint8,uint256,uint8,bytes32,bytes32).selector) {
        env e_metaDelegateByType;
        address delegator_metaDelegateByType;
        uint256 deadline_metaDelegateByType;
        uint8 v_metaDelegateByType;
        bytes32 r_metaDelegateByType;
        bytes32 s_metaDelegateByType;
        uint256 balance_metaDelegateByType = balanceOf(delegator_metaDelegateByType);
        require balance_metaDelegateByType > 0;
        require delegator_metaDelegateByType != account;
        metaDelegateByType(e_metaDelegateByType, delegator_metaDelegateByType, delegatee_metaDelegateByType, VOTING_POWER(), deadline_metaDelegateByType, v_metaDelegateByType, r_metaDelegateByType, s_metaDelegateByType);
    } else if (f.selector == transfer(address, uint256).selector) {
        env e_transfer;
        uint256 amount_transfer;
        uint256 balance_transfer = balanceOf(e_transfer.msg.sender);
        require balance_transfer > 0;
        require e_transfer.msg.sender != account;
        transfer(e_transfer, to_transfer, amount_transfer);
    } else if (f.selector == transferFrom(address, address, uint256).selector) {
        env e_transferFrom;
        address from_transferFrom;
        uint256 amount_transferFrom;
        uint256 balance_transferFrom = balanceOf(from_transferFrom);
        require balance_transferFrom > 0;
        require e_transferFrom.msg.sender != account;
        transferFrom(e_transferFrom, from_transferFrom, to_transferFrom, amount_transferFrom);
    } else if (f.selector == _governancePowerTransferByType(uint104, uint104, address, uint8).selector) {
        env e_governancePowerTransferByType;
        uint104 impactOnDelegationBefore;
        uint104 impactOnDelegationAfter;
        require impactOnDelegationAfter > impactOnDelegationBefore;
        _governancePowerTransferByType(e_governancePowerTransferByType, impactOnDelegationBefore, impactOnDelegationBefore, delegatee_governancePowerTransferByType, VOTING_POWER());
    } else {
        f(e, args);
    }

    uint256 powerAfter = getPowerCurrent(account, VOTING_POWER());

    // Used to check for delegator receiving a transfer
    address votingDelegate_transfer = getVotingDelegate(to_transfer);
    address votingDelegate_transferFrom = getVotingDelegate(to_transferFrom);

    // Power of account can only increase if the "to" address is the account and one of the delegate or transfer functions has been called
    assert powerAfter > powerBefore =>
        (to_delegate == account && f.selector == delegate(address).selector) ||
        (to_delegateByType == account && f.selector == delegateByType(address,uint8).selector) ||
        (delegatee_metaDelegate == account && f.selector == metaDelegate(address,address,uint256,uint8,bytes32,bytes32).selector) ||
        (delegatee_metaDelegateByType == account && f.selector == metaDelegateByType(address,address,uint8,uint256,uint8,bytes32,bytes32).selector) ||
        (to_transfer == account && f.selector == transfer(address, uint256).selector) ||
        (to_transferFrom == account && f.selector == transferFrom(address, address, uint256).selector) ||
        (delegatee_governancePowerTransferByType == account && f.selector == _governancePowerTransferByType(uint104, uint104, address, uint8).selector) ||
        // Checks for delegator receiving a transfer
        (votingDelegate_transfer == account && f.selector == transfer(address, uint256).selector) ||
        (votingDelegate_transferFrom == account && f.selector == transferFrom(address, address, uint256).selector);
}

/**

    RULE 32

    Checks: PROPOSITION_POWER
    Checks method: All
    Outcome: PASSES

    An account's proposition power is increased only when it:
    - Receives transfer of tokens
    - Receives delegation
    - Delegator receives transfer
*/

rule propositionPowerIncreasedOnlyByTransferAndDelegation(){
    env e;
    method f;
    address account;
    calldataarg args;

    uint256 powerBefore = getPowerCurrent(account, PROPOSITION_POWER());

    address to_delegate;
    address to_delegateByType;
    address delegatee_metaDelegate;
    address delegatee_metaDelegateByType;
    address to_transfer;
    address to_transferFrom;
    address delegatee_governancePowerTransferByType;

    if (f.selector == delegate(address).selector) {
        env e_delegate;
        uint256 balance_delegate = balanceOf(e_delegate.msg.sender);
        require balance_delegate > 0;
        require e_delegate.msg.sender != account;
        delegate(e_delegate,to_delegate);
    } else if (f.selector == delegateByType(address,uint8).selector) {
        env e_delegateByType;
        uint256 balance_delegateByType = balanceOf(e_delegateByType.msg.sender);
        require balance_delegateByType > 0;
        require e_delegateByType.msg.sender != account;
        delegateByType(e_delegateByType,to_delegateByType,PROPOSITION_POWER());
    } else if (f.selector == metaDelegate(address,address,uint256,uint8,bytes32,bytes32).selector) {
        env e_metaDelegate;
        address delegator_metaDelegate;
        uint256 deadline_metaDelegate;
        uint8 v_metaDelegate;
        bytes32 r_metaDelegate;
        bytes32 s_metaDelegate;
        uint256 balance_metaDelegate = balanceOf(delegator_metaDelegate);
        require balance_metaDelegate > 0;
        require delegator_metaDelegate != account;
        metaDelegate(e_metaDelegate, delegator_metaDelegate, delegatee_metaDelegate,deadline_metaDelegate,v_metaDelegate,r_metaDelegate,s_metaDelegate);
    } else if (f.selector == metaDelegateByType(address,address,uint8,uint256,uint8,bytes32,bytes32).selector) {
        env e_metaDelegateByType;
        address delegator_metaDelegateByType;
        uint256 deadline_metaDelegateByType;
        uint8 v_metaDelegateByType;
        bytes32 r_metaDelegateByType;
        bytes32 s_metaDelegateByType;
        uint256 balance_metaDelegateByType = balanceOf(delegator_metaDelegateByType);
        require balance_metaDelegateByType > 0;
        require delegator_metaDelegateByType != account;
        metaDelegateByType(e_metaDelegateByType, delegator_metaDelegateByType, delegatee_metaDelegateByType, PROPOSITION_POWER(), deadline_metaDelegateByType, v_metaDelegateByType, r_metaDelegateByType, s_metaDelegateByType);
    } else if (f.selector == transfer(address, uint256).selector) {
        env e_transfer;
        uint256 amount_transfer;
        uint256 balance_transfer = balanceOf(e_transfer.msg.sender);
        require balance_transfer > 0;
        require e_transfer.msg.sender != account;
        transfer(e_transfer, to_transfer, amount_transfer);
    } else if (f.selector == transferFrom(address, address, uint256).selector) {
        env e_transferFrom;
        address from_transferFrom;
        uint256 amount_transferFrom;
        uint256 balance_transferFrom = balanceOf(from_transferFrom);
        require balance_transferFrom > 0;
        require e_transferFrom.msg.sender != account;
        transferFrom(e_transferFrom, from_transferFrom, to_transferFrom, amount_transferFrom);
    } else if (f.selector == _governancePowerTransferByType(uint104, uint104, address, uint8).selector) {
        env e_governancePowerTransferByType;
        uint104 impactOnDelegationBefore;
        uint104 impactOnDelegationAfter;
        require impactOnDelegationAfter > impactOnDelegationBefore;
        _governancePowerTransferByType(e_governancePowerTransferByType, impactOnDelegationBefore, impactOnDelegationBefore, delegatee_governancePowerTransferByType, VOTING_POWER());
    } else {
        f(e, args);
    }

    uint256 powerAfter = getPowerCurrent(account, PROPOSITION_POWER());

    // Used to check for delegator receiving a transfer
    address propositionDelegate_transfer = getPropositionDelegate(to_transfer);
    address propositionDelegate_transferFrom = getPropositionDelegate(to_transferFrom);

    // Power of account can only increase if the "to" address is the account and one of the delegate or transfer functions has been called
    assert powerAfter > powerBefore =>
        (to_delegate == account && f.selector == delegate(address).selector) ||
        (to_delegateByType == account && f.selector == delegateByType(address,uint8).selector) ||
        (delegatee_metaDelegate == account && f.selector == metaDelegate(address,address,uint256,uint8,bytes32,bytes32).selector) ||
        (delegatee_metaDelegateByType == account && f.selector == metaDelegateByType(address,address,uint8,uint256,uint8,bytes32,bytes32).selector) ||
        (to_transfer == account && f.selector == transfer(address, uint256).selector) ||
        (to_transferFrom == account && f.selector == transferFrom(address, address, uint256).selector) ||
        (delegatee_governancePowerTransferByType == account && f.selector == _governancePowerTransferByType(uint104, uint104, address, uint8).selector) ||
        // Checks for delegator receiving a transfer
        (propositionDelegate_transfer == account && f.selector == transfer(address, uint256).selector) ||
        (propositionDelegate_transferFrom == account && f.selector == transferFrom(address, address, uint256).selector);
}

/**

    RULE 33

    Checks method: All
    Outcome: PASSES

    Delegation state change of an account from no delegation to a delegation can only occur if delegate functions are
    called and the sender/delegator is the account
*/

rule delegationStateChange(){
    env e;
    method f;
    calldataarg args;
    address account;

    address to_delegate;
    address to_delegateByType;
    address delegatee_metaDelegate;
    address delegatee_metaDelegateByType;
    address to_transfer;
    address to_transferFrom;
    address delegatee_governancePowerTransferByType;

    env e_delegate;
    env e_delegateByType;
    env e_metaDelegateByType;
    env e_governancePowerTransferByType;

    address delegator_metaDelegate;
    address delegator_metaDelegateByType;

    uint256 delegationStateBefore = getDelegationState(account);

    if (f.selector == delegate(address).selector) {
        require to_delegate != account;
        delegate(e_delegate,to_delegate);
    } else if (f.selector == delegateByType(address,uint8).selector) {
        require to_delegateByType != account;
        delegateByType(e_delegateByType,to_delegateByType,PROPOSITION_POWER());
    } else if (f.selector == metaDelegate(address,address,uint256,uint8,bytes32,bytes32).selector) {
        env e_metaDelegate;
        uint256 deadline_metaDelegate;
        uint8 v_metaDelegate;
        bytes32 r_metaDelegate;
        bytes32 s_metaDelegate;
        require delegatee_metaDelegate != account;
        metaDelegate(e_metaDelegate, delegator_metaDelegate, delegatee_metaDelegate,deadline_metaDelegate,v_metaDelegate,r_metaDelegate,s_metaDelegate);
    } else if (f.selector == metaDelegateByType(address,address,uint8,uint256,uint8,bytes32,bytes32).selector) {
        uint256 deadline_metaDelegateByType;
        uint8 v_metaDelegateByType;
        bytes32 r_metaDelegateByType;
        bytes32 s_metaDelegateByType;
        require delegatee_metaDelegateByType != account;
        metaDelegateByType(e_metaDelegateByType, delegator_metaDelegateByType, delegatee_metaDelegateByType, PROPOSITION_POWER(), deadline_metaDelegateByType, v_metaDelegateByType, r_metaDelegateByType, s_metaDelegateByType);
    }  else if (f.selector == _governancePowerTransferByType(uint104, uint104, address, uint8).selector) {
        uint104 impactOnDelegationBefore;
        uint104 impactOnDelegationAfter;
        require impactOnDelegationAfter > impactOnDelegationBefore;
        _governancePowerTransferByType(e_governancePowerTransferByType, impactOnDelegationBefore, impactOnDelegationBefore, delegatee_governancePowerTransferByType, VOTING_POWER());
    } else {
        f(e, args);
    }

    uint256 delegationStateAfter= getDelegationState(account);

    assert delegationStateBefore == NO_DELEGATION() && (delegationStateAfter == VOTING_DELEGATED() || delegationStateAfter == PROPOSITION_DELEGATED()|| delegationStateAfter == FULL_POWER_DELEGATED()) =>
        (e_delegate.msg.sender == account && f.selector == delegate(address).selector) ||
        (e_delegateByType.msg.sender == account && f.selector == delegateByType(address,uint8).selector) ||
        (delegator_metaDelegate == account && f.selector == metaDelegate(address,address,uint256,uint8,bytes32,bytes32).selector) ||
        (delegator_metaDelegateByType == account && f.selector == metaDelegateByType(address,address,uint8,uint256,uint8,bytes32,bytes32).selector);
}

/**

    RULE 34
    Checks: VOTING_POWER
    Checks Method: delegate
    Outcome: PASSES

    Can not double delegate
    If double delegate, it should:
    - Only change the delegatee's balance once

*/

rule canNotDoubleDelegateVotingPower() {
    env e;
    address delegatee;

    // delegate not to self or to zero
    require delegatee != e.msg.sender && delegatee != 0;

    uint256 delegateeDelegatedBalance = getDelegatedVotingBalance(delegatee);
    // avoid unrealistic delegated balance
    require(delegateeDelegatedBalance < MAX_DELEGATED_BALANCE());
    
    // Verify that the sender doesn't already delegate to bob
    address delegateBefore = getVotingDelegate(e.msg.sender);
    require delegateBefore != delegatee;

    uint256 delegateeVotingPowerBefore = getPowerCurrent(delegatee, VOTING_POWER());
    uint256 delegatorBalance = balanceOf(e.msg.sender);

    // Call delegate twice
    delegate(e, delegatee);
    delegate(e, delegatee);

    // Test the delegate indeed has changed to delegatee
    address delegateAfter = getVotingDelegate(e.msg.sender);
    assert delegateAfter == delegatee;

    // Verify the delegatee's new voting power has not been double counted
    uint256 delegateeVotingPowerAfter = getPowerCurrent(delegatee, VOTING_POWER());
    assert delegateeVotingPowerAfter == delegateeVotingPowerBefore + normalize(delegatorBalance);
}

/**

    RULE 35
    Checks: PROPOSITION_POWER
    Checks Method: delegate
    Outcome: PASSES

    Can not double delegate
    If double delegate, it should:
    - Only change the delegatee's balance once

*/

rule canNotDoubleDelegatePropositionPower() {
    env e;
    address delegatee;

    // delegate not to self or to zero
    require delegatee != e.msg.sender && delegatee != 0;

    uint256 delegateeDelegatedBalance = getDelegatedPropositionBalance(delegatee);
    // avoid unrealistic delegated balance
    require(delegateeDelegatedBalance < MAX_DELEGATED_BALANCE());
    
    // Verify that the sender doesn't already delegate to bob
    address delegateBefore = getPropositionDelegate(e.msg.sender);
    require delegateBefore != delegatee;

    uint256 delegateePropositionPowerBefore = getPowerCurrent(delegatee, PROPOSITION_POWER());
    uint256 delegatorBalance = balanceOf(e.msg.sender);

    // Call delegate twice
    delegate(e, delegatee);
    delegate(e, delegatee);

    // Test the delegate indeed has changed to delegatee
    address delegateAfter = getPropositionDelegate(e.msg.sender);
    assert delegateAfter == delegatee;

    // Verify the delegatee's new Proposition power has not been double counted
    uint256 delegateePropositionPowerAfter = getPowerCurrent(delegatee, PROPOSITION_POWER());
    assert delegateePropositionPowerAfter == delegateePropositionPowerBefore + normalize(delegatorBalance);
}

/**

    RULE 36
    Checks Method: All
    Outcome: PASSES

    If individual balance increases, total supply increases and vice versa
    If individual balance decreases, total supply decreases and vice versa

*/

rule monotonicityBalanceTotalSupply(method f)
    filtered {
        f -> f.selector != transfer(address, uint256).selector
            && f.selector != transferFrom(address, address, uint256).selector
    }
    {
        env e;
        calldataarg args;
        
        uint256 balanceBefore = balanceOf(e.msg.sender);
        mathint totalSupplyBefore = totalSupply();
        
        f(e, args);
        
        uint256 balanceAfter = balanceOf(e.msg.sender);
        mathint totalSupplyAfter = totalSupply();
        
        assert balanceAfter > balanceBefore <=> totalSupplyBefore < totalSupplyAfter;
        assert balanceAfter < balanceBefore <=> totalSupplyBefore > totalSupplyAfter;
    }

/**

    RULE 37
    Checks Method: All
    Outcome: PASSES

    An account's action does not decrease another account's balance

*/

rule senderCanNotDecreaseOtherBalance(method f) 
    filtered {
        f -> f.selector != transferFrom(address, address, uint256).selector
    }
    {
        address sender;
        address other;
        calldataarg args;
        env e;

        require other != sender; 
        
        uint256 otherBalanceBefore = balanceOf(other); 
        require e.msg.sender == sender;

        f(e, args);

        uint256 otherBalanceAfter = balanceOf(other);

        assert otherBalanceAfter >= otherBalanceBefore, "The balance must not decrease"; 
}


/**

   RULE 38
   
   Checks methods: All
   Outcome: PASSES

   Delegation state can only change from delegation functions

*/

rule delegationStateChanges() {
    method f;
    env e;
    calldataarg args;
    address account;

    address stateBefore = getDelegationState(account);

    f(e, args);

    address stateAfter = getDelegationState(account);

    // Only these functions can change the delegation state
    assert stateAfter != stateBefore =>
        f.selector == delegate(address).selector || 
        f.selector == delegateByType(address,uint8).selector ||
        f.selector == metaDelegate(address,address,uint256,uint8,bytes32,bytes32).selector ||
        f.selector == metaDelegateByType(address,address,uint8,uint256,uint8,bytes32,bytes32).selector;
}

/**

   RULE 39
   
   Checks methods: All
   Outcome: PASSES
   
   Delegation state can only change from delegation functions

*/

rule delegationDoesNotChangeTotalSupply() {
    method f;
    env e;
    calldataarg args;
    address account;

    uint256 totalSupplyBefore = totalSupply();

    f(e, args);

    uint256 totalSupplyAfter = totalSupply();

    // These functions can not change totalSupply
    assert totalSupplyAfter != totalSupplyBefore =>
        f.selector != delegate(address).selector &&
        f.selector != delegateByType(address,uint8).selector &&
        f.selector != metaDelegate(address,address,uint256,uint8,bytes32,bytes32).selector &&
        f.selector != metaDelegateByType(address,address,uint8,uint256,uint8,bytes32,bytes32).selector;
}

/**

   RULE 40
   
   Checks methods: All
   Outcome: PASSES
   
   Account can not have voting power greater than total supply

*/
invariant accountCanNotHaveVotingPowerGreaterThanTotalSupply(address account)
    normalize(getDelegatedVotingBalance(account)) <= totalSupply()

/**

   RULE 41
   
   Checks methods: All
   Outcome: PASSES
   
   Account can not have proposition power greater than total supply

*/
invariant accountCanNotHavePropositionPowerGreaterThanTotalSupply(address account)
    normalize(getDelegatedPropositionBalance(account)) <= totalSupply()