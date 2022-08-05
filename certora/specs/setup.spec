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


// ghost mapping(address => uint8) ghostBalance
// {
//     init_state axiom forall address a. ghostBalance[a] == 0;
// }

// hook Sload uint256 balance _balaces[KEY address addr] STORAGE {
//     require ghostBalance[addr] == balance;
// }

// hook Sstore _balances[KEY address addr] uint256 balance (uint256 old_balance) STORAGE {
//     ghostBalance[addr] = balance;
// }

/**

    RULE 1

    Condition: Account is not receiving delegation of power from anybody and that account is not delegating that power to anybody
    Checks: VOTING_POWER
    Checks Methods: All

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

    Transfering tokens of amount z >= 0 from account1 to account2 should decrease voting power of account1 by z and increase power of account2 by z

*/
rule transferChangesVotingPower(address account1, address account2, uint256 amount) {
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

    Transfering tokens of amount z >= 0 from account1 to account2 should decrease proposition power of account1 by z and increase power of account2 by z 

*/
rule transferChangesPropositionPower(address account1, address account2, uint256 amount) {
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

    Delegating from account1 to account2 will increase account2's power by account1's balance

*/
rule delegatingChangesVotingPower(address account1, address account2) {
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

    Delegating from account1 to account2 will increase account2's power by account1's balance

*/
rule delegatingChangesPropositionPower(address account1, address account2) {
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

    Transfering tokens of amount z >= 0 from account1 to account2 should keep the voting power of account1 the same (i.e. zero)
    and decrease delegatee1's voting power by z and increase account2's voting power by z

*/
rule transferChangesVotingPowerWhenAccount1DelegatesAndAccount2DoesNotDelegate(address account1, address account2, uint256 amount) {
    env e;
    address delegatee1;

    // require the accounts are not the same
    require account1 != account2;

    // Require that account1 is delegating power to delegatee1
    address votingDelegatee = getVotingDelegate(account1);
    require votingDelegatee == delegatee1;

    // Require the account is not delegating to nobody (i.e. itself or zero account)
    require delegatee1 != account1;
    require delegatee1 != 0;

    uint8 account1DelegationState = getDelegationState(account1);
    require account1DelegationState == VOTING_DELEGATED();

    // Account1 Balance before
    uint256 account1BalanceBefore = balanceOf(account1);

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
    uint256 account1BalanceAfter = balanceOf(account1);

    assert account1VotingPowerAfter == account1VotingPowerBefore, "account1 voting power after must not change after transfer because it was delegating";
    assert delegatee1 != account2 => account2VotingPowerAfter == account2VotingPowerBefore + amount, "account2's power must increase by amount of transfer";    
}

