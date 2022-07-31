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
    delegateByType(address delegatee, uint8 delegationType)
    metaDelegate(address, address, uint256, uint8, bytes32, bytes32)
    metaDelegateByType(address delegator, address delegatee, uint8 delegationType, uint256 deadline, uint8 v, bytes32 r, bytes32 s)
    permit(address owner, address spender, uint256 value, uint256 deadline, uint8 v, bytes32 r, bytes32 s)
    getPowerCurrent(address user, uint8 delegationType) returns (uint256) envfree
    getPowersCurrent(address user) returns (uint256, uint256) envfree
    getBalance(address user) returns (uint104) envfree
    getDelegatedPropositionBalance(address user) returns (uint72) envfree
    getDelegatedVotingBalance(address user) returns (uint72) envfree
    getDelegatingProposition(address user) returns (bool) envfree
    getDelegatingVoting(address user) returns (bool) envfree
    getVotingDelegate(address user) returns (address) envfree
    getPropositionDelegate(address user) returns (address) envfree
    getNonce(address user) returns (uint256) envfree
    getAllowance(address owner, address spender) returns (uint256) envfree
    getDelegationState(address user) returns (uint8) envfree
}

/**

    Constants

*/
// GovernancyType enum from the token contract
definition VOTING_POWER() returns uint8 = 0;
definition PROPOSITION_POWER() returns uint8 = 1;

definition DELEGATED_POWER_DIVIDER() returns uint256 = 10^10;

definition NO_DELEGATION() returns uint8 = 0;

definition VOTING_DELEGATED() returns uint8 = 1;

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


///////////////////////////////////////  ADD SPECS - Parth Patel ////////////////////////////////////////

ghost mathint delegatedPropositionBalanceSum {
    init_state axiom delegatedPropositionBalanceSum == 0;
}

ghost mathint delegatedVotingBalanceSum {
    init_state axiom delegatedVotingBalanceSum == 0;
}

ghost mathint sumBalances {
    init_state axiom sumBalances == 0;
}

hook Sstore _balances[KEY address user].balance uint104 balance
    (uint104 old_balance) STORAGE {
        sumBalances = sumBalances - to_mathint(old_balance) + to_mathint(balance);
    }

hook Sstore _balances[KEY address user].delegatedPropositionBalance uint72 delegatedPropositionBalance
    (uint72 oldDelegatedPropositionBalance) STORAGE {
        delegatedPropositionBalanceSum = delegatedPropositionBalanceSum 
        - to_mathint(oldDelegatedPropositionBalance) 
        + to_mathint(delegatedPropositionBalance);
    }

hook Sstore _balances[KEY address user].delegatedVotingBalance uint72 delegatedVotingBalance
    (uint72 oldDelegatedVotingBalance) STORAGE {
        delegatedVotingBalanceSum = delegatedVotingBalanceSum 
        - to_mathint(oldDelegatedVotingBalance) 
        + to_mathint(delegatedVotingBalance);
    }

invariant totalSupplyEqualsBalances()
    sumBalances == totalSupply()

invariant totalSupplyGreaterThanSumOFBalanceOfUser(address user1, address user2) 
    balanceOf(user1) + balanceOf(user2) <= totalSupply()

/**
    invariant
    TotalSupply is greater than or equal to sum of delegated proposition balance
*/
invariant totalSupplyGreaterOrEqualsDelegatedPropositionBalanceSum(address user1, address user2)
    delegatedPropositionBalanceSum <= normalize(totalSupply())
    { 
        preserved
        {
            requireInvariant totalSupplyGreaterThanSumOFBalanceOfUser(user1, user2);
        }
    }

/**
    invariant
    TotalSupply is greater than or equal to sum of delegated voting balance
*/
invariant totalSupplyGreaterOrEqualsDelegatedVotingBalanceSum(address user1, address user2)
    delegatedVotingBalanceSum <= normalize(totalSupply())
     { 
        preserved
        {
            requireInvariant totalSupplyGreaterThanSumOFBalanceOfUser(user1, user2);
        }
    }


/**
    invariant
    Zero address doesn't hold any tokens and doesn't have Proposition and Voting Power

*/
invariant zeroAddressDoesNotHaveBalanceOrPower() 
    balanceOf(0) == 0 && getDelegatedPropositionBalance(0) == 0 && getDelegatedVotingBalance(0) == 0

invariant addressZeroDoesNotHaveAnyPower()
    getBalance(0) == 0 && getPowerCurrent(0, VOTING_POWER()) == 0 && getPowerCurrent(0, PROPOSITION_POWER()) == 0

/**
    Rule
    Voting delegate and Proposition delegate can only be changed by following 4 methods
    delegate, delegateByType, metaDelegate, metaDelegateByType
*/
rule votingAndPropositionDelegatedChangesCanOnlyBeDoneByCertainMethods() {
    address user;
    method f;
    env e;
    calldataarg args;

    address votingDelegateBefore = getVotingDelegate(user);
    address propositionDelegateBefore = getPropositionDelegate(user);

    f(e, args);

    address votingDelegateAfter = getVotingDelegate(user);
    address propositionDelegateAfter = getPropositionDelegate(user);

    // only following function can change the voting or proposition delegate
    assert 
    (votingDelegateBefore != votingDelegateAfter || 
    propositionDelegateBefore != propositionDelegateAfter) =>
        f.selector == delegate(address).selector || 
        f.selector == delegateByType(address,uint8).selector ||
        f.selector == metaDelegate(address,address,uint256,uint8,bytes32,bytes32).selector ||
        f.selector == metaDelegateByType(address,address,uint8,uint256,uint8,bytes32,bytes32).selector, 
        "voting and proposition changes can only be done by delegate, delegateByType, metaDelegate, metaDelegateByType";
}

/**
    delegateByType and metaDelegateByType can be called by Voting and Proposition GovernancePowerType.
    delegating and metadelegating by voting should not affect proposition of user
    delegating and metadelegating by proposition should not affect voting of user
*/
rule votingDelegationDoesNotAffectPropositionDelegationAndViceVersa() {
    address user;
    address delegatee;
    env e;
    uint256 deadline;
    uint8 v;
    bytes32 r;
    bytes32 s;

    storage initialState = lastStorage;
    address votingDelegateBefore = getVotingDelegate(user);
    //delegating by proposition
    delegateByType(e, delegatee, PROPOSITION_POWER());
    address votingDelegateAfter = getVotingDelegate(user);
    assert(votingDelegateBefore == votingDelegateAfter, 
    "delegating by proposition type should not affect voting delegate");

    address propositionDelegateBefore = getPropositionDelegate(user) at initialState;
    //delegating by voting
    delegateByType(e, delegatee, VOTING_POWER());
    address propositionDelegateAfter = getPropositionDelegate(user);
    assert(propositionDelegateBefore == propositionDelegateAfter, 
    "delegating by voting type should not affect proposition delegate");


    address propositionDelegateBefore1 = getPropositionDelegate(user) at initialState;
    // delegating by voting
    metaDelegateByType(e, user, delegatee, VOTING_POWER(), deadline, v, r, s);
    address propositionDelegateAfter1 = getPropositionDelegate(user);
    assert(propositionDelegateBefore1 == propositionDelegateAfter1, 
    "meta delegating by voting type should not affect proposition delegate");

    address votingDelegateBefore1 = getVotingDelegate(user) at initialState;
    //delegating by proposition
    metaDelegateByType(e, user, delegatee, PROPOSITION_POWER(), deadline, v, r, s);
    address votingDelegateAfter1 = getVotingDelegate(user);
    assert(votingDelegateBefore1 == votingDelegateAfter1, 
    "meta delegating by proposition type should not affect voting delegate");

}

/**
    nonce of user can only be changed by permit or meta functions
*/
rule NonceCanOnlyBeChangedByMetaFunctions() {
    address user;
    env e;
    calldataarg args;
    method f;

    uint256 nonceBefore = getNonce(user);

    f(e, args);

    uint256 nonceAfter = getNonce(user);

    assert nonceBefore != nonceAfter => 
        f.selector == metaDelegate(address,address,uint256,uint8,bytes32,bytes32).selector ||
        f.selector == metaDelegateByType(address,address,uint8,uint256,uint8,bytes32,bytes32).selector ||
        f.selector == permit(address,address,uint256,uint256,uint8,bytes32,bytes32).selector,
        "nonce can only be changed by permit, metaDelegate and metaDelegateByType";
}

/**
    Integrity of permit function
    Successful permit function increases the nonce of owner by 1 and also changes the allowance of owner to spender
*/
rule permitIntegrity() {
    env e;
    address owner;
    address spender;
    uint256 value;
    uint256 deadline;
    uint8 v;
    bytes32 r;
    bytes32 s;

    uint256 allowanceBefore = getAllowance(owner, spender);
    mathint nonceBefore = getNonce(owner);

    //checking this because function is using unchecked math and such a high nonce is unrealistic
    require nonceBefore < max_uint;

    permit(e, owner, spender, value, deadline, v, r, s);

    uint256 allowanceAfter = getAllowance(owner, spender);
    mathint nonceAfter = getNonce(owner);

    assert allowanceAfter == value, "permit increases allowance of owner to spender on success";
    assert nonceAfter == nonceBefore + 1, "successful call to permit function increases nonce of owner by 1";
}

rule permitDoesNotIntefereForOtherOwner() {
    env e;
    address owner1;
    address owner2;
    address spender;
    uint256 value;
    uint256 deadline;
    uint8 v;
    bytes32 r;
    bytes32 s;

    require owner1 != owner2;

    uint256 allowanceOfOtherUserBefore = getAllowance(owner2, spender);
    uint256 nonceOfOtherUserBefore = getNonce(owner2);

    permit(e, owner1, spender, value, deadline, v, r, s);

    uint256 allowanceOfOtherUserAfter = getAllowance(owner2, spender);
    uint256 nonceOfOtherUserAfter = getNonce(owner2);

    assert allowanceOfOtherUserBefore == allowanceOfOtherUserAfter, "allowance of other user should not change";
    assert nonceOfOtherUserBefore == nonceOfOtherUserAfter, "nonce of other user should not change";

}

rule delegateIntegrity() {
    env e;
    address delegatee;

    require delegatee != e.msg.sender;
    require delegatee != 0;

    mathint votingPowerBefore = getPowerCurrent(delegatee, VOTING_POWER());
    mathint propositionPowerBefore = getPowerCurrent(delegatee, PROPOSITION_POWER());
    address votingDelegateBefore = getVotingDelegate(e.msg.sender);
    address propositionDelegateBefore = getPropositionDelegate(e.msg.sender);
    mathint delegatedVotingBalanceBefore = getDelegatedVotingBalance(delegatee);
    mathint delegatedPropositionBalanceBefore = getDelegatedPropositionBalance(delegatee);
    uint256 balanceOfSenderBefore = getBalance(e.msg.sender);

    delegate(e, delegatee);

    mathint votingPowerAfter = getPowerCurrent(delegatee, VOTING_POWER());
    mathint propositionPowerAfter = getPowerCurrent(delegatee, PROPOSITION_POWER());
    address votingDelegateAfter = getVotingDelegate(e.msg.sender);
    address propositionDelegateAfter = getPropositionDelegate(e.msg.sender);
    mathint delegatedVotingBalanceAfter = getDelegatedVotingBalance(delegatee);
    mathint delegatedPropositionBalanceAfter = getDelegatedPropositionBalance(delegatee);
    mathint balanceOfSenderAfter = getBalance(e.msg.sender);

    assert delegatee != votingDelegateBefore => votingPowerBefore + normalize(balanceOfSenderBefore) == votingPowerAfter, 
    "voting power increases by balance of sender when delegate is called";
    assert delegatee!=propositionDelegateBefore => propositionPowerBefore+normalize(balanceOfSenderBefore)==propositionPowerAfter,     
    "proposition power increases by balance of sender when delegate is called";

    assert delegatee != votingDelegateBefore => delegatedVotingBalanceBefore + balanceOfSenderBefore/DELEGATED_POWER_DIVIDER() == delegatedVotingBalanceAfter,
    "voting delegate balance increases by balance of sender when delegate is called";
    assert delegatee != propositionDelegateBefore => delegatedPropositionBalanceBefore + balanceOfSenderBefore/DELEGATED_POWER_DIVIDER() == delegatedPropositionBalanceAfter,
    "proposition delegate balance increases by balance of sender when delegate is called";

    assert delegatee != votingDelegateBefore => votingDelegateBefore != votingDelegateAfter,
    "voting delegate changes when delegate is called";
    assert delegatee != propositionDelegateBefore => propositionDelegateBefore != propositionDelegateAfter,
    "proposition delegate changes when delegate is called";

    assert votingDelegateAfter == propositionDelegateAfter, 
    "voting delegate and proposition delegate are same after delegate is called";

    assert balanceOfSenderBefore == balanceOfSenderAfter,
    "balance must remain same on delegate";

}

rule delegateByTypeIntegrity() {
    env e;
    address votingDelegatee;
    address propositionDelegatee;

    require votingDelegatee != e.msg.sender;
    require votingDelegatee != 0;

    require propositionDelegatee != e.msg.sender;
    require propositionDelegatee != 0;

    mathint votingPowerBefore = getPowerCurrent(votingDelegatee, VOTING_POWER());
    mathint propositionPowerBefore = getPowerCurrent(propositionDelegatee, PROPOSITION_POWER());
    address votingDelegateBefore = getVotingDelegate(e.msg.sender);
    address propositionDelegateBefore = getPropositionDelegate(e.msg.sender);
    mathint delegatedVotingBalanceBefore = getDelegatedVotingBalance(votingDelegatee);
    mathint delegatedPropositionBalanceBefore = getDelegatedPropositionBalance(propositionDelegatee);
    uint256 balanceOfSenderBefore = getBalance(e.msg.sender);

    delegateByType(e, votingDelegatee, VOTING_POWER());
    delegateByType(e, propositionDelegatee, PROPOSITION_POWER());

    mathint votingPowerAfter = getPowerCurrent(votingDelegatee, VOTING_POWER());
    mathint propositionPowerAfter = getPowerCurrent(propositionDelegatee, PROPOSITION_POWER());
    address votingDelegateAfter = getVotingDelegate(e.msg.sender);
    address propositionDelegateAfter = getPropositionDelegate(e.msg.sender);
    mathint delegatedVotingBalanceAfter = getDelegatedVotingBalance(votingDelegatee);
    mathint delegatedPropositionBalanceAfter = getDelegatedPropositionBalance(propositionDelegatee);
    mathint balanceOfSenderAfter = getBalance(e.msg.sender);

    assert votingDelegatee != votingDelegateBefore => votingPowerBefore + normalize(balanceOfSenderBefore) == votingPowerAfter, 
    "voting power increases by balance of sender when delegateByType is called";
    assert propositionDelegatee != propositionDelegateBefore => propositionPowerBefore+normalize(balanceOfSenderBefore)==propositionPowerAfter,     
    "proposition power increases by balance of sender when delegateByType is called";

    assert votingDelegatee != votingDelegateBefore => delegatedVotingBalanceBefore + balanceOfSenderBefore/DELEGATED_POWER_DIVIDER() == delegatedVotingBalanceAfter,
    "voting delegate balance increases by balance of sender when delegateByType is called";
    assert propositionDelegatee != propositionDelegateBefore => delegatedPropositionBalanceBefore + balanceOfSenderBefore/DELEGATED_POWER_DIVIDER() == delegatedPropositionBalanceAfter,
    "proposition delegate balance increases by balance of sender when delegateByType is called";

    assert votingDelegatee != votingDelegateBefore => votingDelegateBefore != votingDelegateAfter,
    "voting delegate changes when delegateByType is called";
    assert propositionDelegatee != propositionDelegateBefore => propositionDelegateBefore != propositionDelegateAfter,
    "proposition delegate changes when delegateByType is called";

    assert votingDelegatee != propositionDelegatee => votingDelegateAfter != propositionDelegateAfter, 
    "voting delegate and proposition delegate may not be same when delegateByType is called";

    assert balanceOfSenderBefore == balanceOfSenderAfter,
    "balance must remain same on delegateByType";
}

rule equivalenceOfDelegateAndDelegateByType() {

    env e;
    address delegatee;

    require delegatee != e.msg.sender;
    require delegatee != 0;

    storage initialState = lastStorage;

    address votingDelegateBeforeDelegate = getVotingDelegate(e.msg.sender);
    address propositionDelegateBeforeDelegate = getPropositionDelegate(e.msg.sender);
    mathint delegatedVotingBalanceBeforeDelegate = getDelegatedVotingBalance(delegatee);
    mathint delegatedPropositionBalanceBeforeDelegate = getDelegatedPropositionBalance(delegatee);
    mathint votingPowerBeforeDelegate = getPowerCurrent(delegatee, VOTING_POWER());
    mathint propositionPowerBeforeDelegate = getPowerCurrent(delegatee, PROPOSITION_POWER());

    delegate(e, delegatee);

    address votingDelegateAfterDelegate = getVotingDelegate(e.msg.sender);
    address propositionDelegateAfterDelegate = getPropositionDelegate(e.msg.sender);
    mathint delegatedVotingBalanceAfterDelegate = getDelegatedVotingBalance(delegatee);
    mathint delegatedPropositionBalanceAfterDelegate = getDelegatedPropositionBalance(delegatee);
    mathint votingPowerAfterDelegate = getPowerCurrent(delegatee, VOTING_POWER());
    mathint propositionPowerAfterDelegate = getPowerCurrent(delegatee, PROPOSITION_POWER());

    address votingDelegateBeforeDelegateType = getVotingDelegate(e.msg.sender) at initialState;
    address propositionDelegateBeforeDelegateType = getPropositionDelegate(e.msg.sender);
    mathint votingPowerBeforeDelegateType = getPowerCurrent(delegatee, VOTING_POWER());
    mathint propositionPowerBeforeDelegateType = getPowerCurrent(delegatee, PROPOSITION_POWER());
    mathint delegatedVotingBalanceBeforeDelegateType = getDelegatedVotingBalance(delegatee);
    mathint delegatedPropositionBalanceBeforeDelegateType = getDelegatedPropositionBalance(delegatee);

    delegateByType(e, delegatee, VOTING_POWER());
    delegateByType(e, delegatee, PROPOSITION_POWER());

    address votingDelegateAfterDelegateType = getVotingDelegate(e.msg.sender);
    address propositionDelegateAfterDelegateType = getPropositionDelegate(e.msg.sender);
    mathint votingPowerAfterDelegateType = getPowerCurrent(delegatee, VOTING_POWER());
    mathint propositionPowerAfterDelegateType = getPowerCurrent(delegatee, PROPOSITION_POWER());
    mathint delegatedVotingBalanceAfterDelegateType = getDelegatedVotingBalance(delegatee);
    mathint delegatedPropositionBalanceAfterDelegateType = getDelegatedPropositionBalance(delegatee);

    assert votingPowerAfterDelegate == votingPowerAfterDelegateType,
    "voting power should be same after delegate and delegateByType of voting power";

    assert propositionPowerAfterDelegate == propositionPowerAfterDelegateType,
    "proposition delegate should be same after delegate and delegateByType of proposition power";

    assert votingDelegateAfterDelegate == votingDelegateAfterDelegateType, 
    "voting delegate should be same after delegate and delegateByType of voting power";

    assert propositionDelegateAfterDelegate == propositionDelegateAfterDelegateType,
    "proposition delegate should be same after delegate and delegateByType of proposition power";

    assert delegatedVotingBalanceAfterDelegate == delegatedVotingBalanceAfterDelegateType,
    "delegated voting balance should be equal after delegate and delegateByType of voting power";

    assert delegatedPropositionBalanceAfterDelegate == delegatedPropositionBalanceAfterDelegateType,
    "delegated proposition balance should be equal after delegate and delegateByType of proposition power";

}

rule delegatingSecondTimeResetTheStateOfFirstDelegatee() {
    address delegatee1;
    address delegatee2;
    address deadline;
    uint8 v;
    bytes32 r;
    bytes32 s;
    env e;
    storage initialState = lastStorage;

    require delegatee1 != delegatee2;
    require delegatee1 != 0 && delegatee2 != 0;
    require e.msg.sender != 0 && e.msg.sender != delegatee1 && e.msg.sender != delegatee2;

    uint256 balanceOfSenderBefore = getBalance(e.msg.sender);

    delegate(e, delegatee1);

    mathint votingDelegatedBalanceOfDelegatee1BeforeDelegate = getDelegatedVotingBalance(delegatee1);
    mathint propositionDelegatedBalanceOfDelegatee1BeforeDelegate = getDelegatedPropositionBalance(delegatee1);
    mathint votingDelegatedBalanceOfDelegatee2BeforeDelegate = getDelegatedVotingBalance(delegatee2);
    mathint propositionDelegatedBalanceOfDelegatee2BeforeDelegate = getDelegatedPropositionBalance(delegatee2);

    delegate(e, delegatee2);

    mathint votingDelegatedBalanceOfDelegatee1AfterDelegate = getDelegatedVotingBalance(delegatee1);
    mathint propositionDelegatedBalanceOfDelegatee1AfterDelegate = getDelegatedPropositionBalance(delegatee1);
    mathint votingDelegatedBalanceOfDelegatee2AfterDelegate = getDelegatedVotingBalance(delegatee2);
    mathint propositionDelegatedBalanceOfDelegatee2AfterDelegate = getDelegatedPropositionBalance(delegatee2);
    mathint balanceOfSenderAfter = getBalance(e.msg.sender);

    assert votingDelegatedBalanceOfDelegatee1AfterDelegate + balanceOfSenderBefore/DELEGATED_POWER_DIVIDER() == votingDelegatedBalanceOfDelegatee1BeforeDelegate;
    assert propositionDelegatedBalanceOfDelegatee1AfterDelegate + balanceOfSenderBefore/DELEGATED_POWER_DIVIDER() == propositionDelegatedBalanceOfDelegatee1BeforeDelegate;
    assert votingDelegatedBalanceOfDelegatee2BeforeDelegate + balanceOfSenderBefore/DELEGATED_POWER_DIVIDER() == votingDelegatedBalanceOfDelegatee2AfterDelegate;
    assert propositionDelegatedBalanceOfDelegatee2BeforeDelegate + balanceOfSenderBefore/DELEGATED_POWER_DIVIDER() == propositionDelegatedBalanceOfDelegatee2AfterDelegate;
    assert balanceOfSenderBefore == balanceOfSenderAfter;
}

rule delegationToItselfOrZeroAddressDoesNothing() {
    address owner;
    address user;
    uint256 deadline;
    uint8 v;
    bytes32 r;
    bytes32 s;
    env e;
    address to;   
    storage initialState = lastStorage;

    uint256 votingPowerBeforeDelegate = getPowerCurrent(e.msg.sender, VOTING_POWER());
    uint256 propositionPowerBeforeDelegate = getPowerCurrent(e.msg.sender, PROPOSITION_POWER());
    address votingDelegateBeforeDelegate = getVotingDelegate(e.msg.sender);
    address propositionDelegateBeforeDelegate = getPropositionDelegate(e.msg.sender);

    // check that not delegated to anything before
    require votingDelegateBeforeDelegate == 0 && propositionDelegateBeforeDelegate == 0;

    delegate(e, to);

    uint256 votingPowerAfterDelegate = getPowerCurrent(e.msg.sender, VOTING_POWER());
    uint256 propositionPowerAfterDelegate = getPowerCurrent(e.msg.sender, PROPOSITION_POWER());
    address votingDelegateAfterDelegate = getVotingDelegate(e.msg.sender);
    address propositionDelegateAfterDelegate = getPropositionDelegate(e.msg.sender);

    assert (
        to == 0 || to == e.msg.sender
    ) => (
        votingPowerBeforeDelegate == votingPowerAfterDelegate &&
        propositionPowerBeforeDelegate == propositionPowerAfterDelegate &&
        votingDelegateAfterDelegate == 0 &&
        propositionDelegateAfterDelegate ==  0
    ), "Delegating to zero address or own address doesn't change anything";

    uint256 votingPowerBeforeDelegateByType = getPowerCurrent(e.msg.sender, VOTING_POWER()) at initialState;
    address votingDelegateBeforeDelegateByType = getVotingDelegate(e.msg.sender);

    // check that not delegated to anything before
    require votingDelegateBeforeDelegateByType == 0;

    delegateByType(e, to, VOTING_POWER());

    uint256 votingPowerAfterDelegateByType = getPowerCurrent(e.msg.sender, VOTING_POWER());
    address votingDelegateAfterDelegateByType = getVotingDelegate(e.msg.sender);

    assert (
        to == 0 || to == e.msg.sender
    ) => (
        votingPowerBeforeDelegateByType == votingPowerAfterDelegateByType &&
        votingDelegateAfterDelegateByType == 0
    ), "DelegatingByType(Voting) to zero address or own address doesn't change anything";

    uint256 propositionPowerBeforeDelegateByType = getPowerCurrent(e.msg.sender, PROPOSITION_POWER()) at initialState;
    address propositionDelegateBeforeDelegateByType = getPropositionDelegate(e.msg.sender);

    // check that not delegated to anything before
    require propositionDelegateBeforeDelegateByType == 0;

    delegateByType(e, to, PROPOSITION_POWER());

    uint256 propositionPowerAfterDelegateByType = getPowerCurrent(e.msg.sender, PROPOSITION_POWER());
    address propositionDelegateAfterDelegateByType = getPropositionDelegate(e.msg.sender);

    assert (
        to == 0 || to == e.msg.sender
    ) => (
        propositionPowerBeforeDelegateByType == propositionPowerAfterDelegateByType &&
        propositionDelegateAfterDelegateByType == 0
    ), "DelegatingByType(Proposition) to zero address or own address doesn't change anything";

    uint256 votingPowerBeforeMetaDelegate = getPowerCurrent(e.msg.sender, VOTING_POWER()) at initialState;
    uint256 propositionPowerBeforeMetaDelegate = getPowerCurrent(e.msg.sender, PROPOSITION_POWER());
    address votingDelegateBeforeMetaDelegate = getVotingDelegate(e.msg.sender);
    address propositionDelegateBeforeMetaDelegate = getPropositionDelegate(e.msg.sender);

    // not delegated to anything before
    require votingDelegateBeforeMetaDelegate == 0 && propositionDelegateBeforeMetaDelegate == 0;

    metaDelegate(e, e.msg.sender, to, deadline, v, r, s);

    uint256 votingPowerAfterMetaDelegate = getPowerCurrent(e.msg.sender, VOTING_POWER());
    uint256 propositionPowerAfterMetaDelegate = getPowerCurrent(e.msg.sender, PROPOSITION_POWER());
    address votingDelegateAfterMetaDelegate = getVotingDelegate(e.msg.sender);
    address propositionDelegateAfterMetaDelegate = getPropositionDelegate(e.msg.sender);

    assert (
        to == 0 || to == e.msg.sender
    ) => (
        votingPowerBeforeMetaDelegate == votingPowerAfterMetaDelegate &&
        propositionPowerBeforeMetaDelegate == propositionPowerAfterMetaDelegate &&
        votingDelegateAfterMetaDelegate == 0 &&
        propositionDelegateAfterMetaDelegate ==  0
    ), "Meta Delegating to zero address or own address doesn't change anything";

    uint256 votingPowerBeforeMetaDelegateByType = getPowerCurrent(e.msg.sender, VOTING_POWER()) at initialState;
    address votingDelegateBeforeMetaDelegateByType = getVotingDelegate(e.msg.sender);

    // not delegated to anything before
    require votingDelegateBeforeMetaDelegateByType == 0;
    
    metaDelegateByType(e, e.msg.sender, to, VOTING_POWER(), deadline, v, r, s);

    uint256 votingPowerAfterMetaDelegateByType = getPowerCurrent(e.msg.sender, VOTING_POWER());
    address votingDelegateAfterMetaDelegateByType = getVotingDelegate(e.msg.sender);

    assert (
        to == 0 || to == e.msg.sender
    ) => (
        votingPowerBeforeMetaDelegateByType == votingPowerAfterMetaDelegateByType &&
        votingDelegateAfterMetaDelegateByType == 0 
    ), "Meta Delegating(Voting) to zero address or own address doesn't change anything";


    uint256 propositionPowerBeforeMetaDelegateByType = getPowerCurrent(e.msg.sender, PROPOSITION_POWER()) at initialState;
    address propositionDelegateBeforeMetaDelegateByType = getPropositionDelegate(e.msg.sender);

    // check that not delegated to anything before
    require propositionDelegateBeforeMetaDelegateByType == 0;

    metaDelegateByType(e, e.msg.sender, to, PROPOSITION_POWER(), deadline, v, r, s);

    uint256 propositionPowerAfterMetaDelegateByType = getPowerCurrent(e.msg.sender, PROPOSITION_POWER());
    address propositionDelegateAfterMetaDelegateByType = getPropositionDelegate(e.msg.sender);

     assert (
        to == 0 || to == e.msg.sender
    ) => (
        propositionPowerBeforeMetaDelegateByType == propositionPowerAfterMetaDelegateByType &&
        propositionDelegateAfterMetaDelegateByType == 0 
    ), "Meta Delegating(Proposition) to zero address or own address doesn't change anything";

}


rule transferIncreasesPowerOfReceipient() {
    env e;
    address recepient;
    uint256 amount;

    require e.msg.sender != recepient;
    require amount > 0;

    address votingDelegateOfSender = getVotingDelegate(e.msg.sender);
    address propositionDelegateOfSender = getPropositionDelegate(e.msg.sender);

    //power remains same if delegate is recepient address
    require votingDelegateOfSender != recepient && propositionDelegateOfSender != recepient;


    uint256 votingPowerOfRecepientBefore = getPowerCurrent(recepient, VOTING_POWER());
    uint256 propositionPoweOfRecepientrBefore = getPowerCurrent(recepient, PROPOSITION_POWER());
    uint256 balanceBefore = getBalance(e.msg.sender);

    transfer(e, recepient, amount);

    uint256 votingPowerOfRecepientAfter = getPowerCurrent(recepient, VOTING_POWER());
    uint256 propositionPowerOfRecepientAfter = getPowerCurrent(recepient, PROPOSITION_POWER());
    uint256 balanceAfter = getBalance(e.msg.sender);

    assert balanceBefore > balanceAfter, "balance of sender should decrease";

    assert votingPowerOfRecepientBefore <= votingPowerOfRecepientAfter, 
    "voting power of recepient should increase on transfer";
    assert propositionPoweOfRecepientrBefore <= propositionPowerOfRecepientAfter, 
    "proposition power of recepeint should increase on transfer";

}

rule powerComprisesOfBalanceAndDelegationByOther() {
    env e;
    address user;

    mathint balanceOfUser = balanceOf(user);
    mathint delegatedVotingBalanceOfUser = getDelegatedVotingBalance(user);
    mathint delegatedPropositionBalanceOfUser = getDelegatedPropositionBalance(user);
    mathint votingPowerOfUser = getPowerCurrent(user, VOTING_POWER());
    mathint propositionPowerOfUser = getPowerCurrent(user, PROPOSITION_POWER());

    assert votingPowerOfUser > 0 => balanceOfUser > 0 || delegatedVotingBalanceOfUser > 0, 
    "voting power comprises of balance or delegation of voting power from other";

    assert propositionPowerOfUser > 0 => balanceOfUser > 0 || delegatedPropositionBalanceOfUser > 0, 
    "proposition power comprises of balance or delegation of proposition power from other";

}

rule delegateNotTransitive() {
    env e1;
    env e2;
    address user1;
    address user2;
    address user3;
    uint256 deadline;
    uint8 v;
    bytes32 r;
    bytes32 s;
    storage initialState = lastStorage;

    require e1.msg.sender == user1;
    require e2.msg.sender == user2;
    require user1 != user3 && user2 != user3;
    require user1 != 0 && user2 != 0 && user3 != 0;

    // user1 delegates to user2
    delegate(e1, user2);
    // user2 delegates to user3
    delegate(e2, user3);

    address votingDelegateOfUser1AfterDelegate = getVotingDelegate(user1);
    address propositionDelegateOfUser1AfterDelegate = getPropositionDelegate(user1);

    assert votingDelegateOfUser1AfterDelegate != user3, "delegate not transitive";
    assert propositionDelegateOfUser1AfterDelegate != user3, "delegate not transitive";

    // user1 delegates to user2
    delegateByType(e1, user2, VOTING_POWER()) at initialState;
    // user2 delegates to user3
    delegateByType(e2, user3, VOTING_POWER());

    address votingDelegateOfUser1AfterDelegateByType = getVotingDelegate(user1);
    assert votingDelegateOfUser1AfterDelegateByType != user3, "delegate not transitive";

    // user1 delegates to user2
    delegateByType(e1, user2, PROPOSITION_POWER()) at initialState;
    // user2 delegates to user3
    delegateByType(e2, user3, PROPOSITION_POWER());

    address propositionDelegateOfUser1AfterDelegateByType = getPropositionDelegate(user1);
    assert propositionDelegateOfUser1AfterDelegateByType != user3, "delegate not transitive";

    // user1 delegates to user2
    metaDelegate(e1, user1, user2, deadline, v, r, s) at initialState;
    // user2 delegates to user3
    metaDelegate(e2, user2, user3, deadline, v, r, s);

    address votingDelegateOfUser1AfterMetaDelegate = getVotingDelegate(user1);
    address propositionDelegateOfUser1AfterMetaDelegate = getPropositionDelegate(user1);

    assert votingDelegateOfUser1AfterMetaDelegate != user3, "delegate not transitive";
    assert propositionDelegateOfUser1AfterMetaDelegate != user3, "delegate not transitive";

    // user1 delegates to user2
    metaDelegateByType(e1, user1, user2, VOTING_POWER(), deadline, v, r, s) at initialState;
    // user2 delegates to user3
    metaDelegateByType(e2, user2, user3, VOTING_POWER(), deadline, v, r, s);

    address votingDelegateOfUser1AfterMetaDelegateByType = getVotingDelegate(user1);
    assert votingDelegateOfUser1AfterMetaDelegateByType != user3, "delegate not transitive";

    // user1 delegates to user2
    metaDelegateByType(e1, user1, user2, PROPOSITION_POWER(), deadline, v, r, s) at initialState;
    // user2 delegates to user3
    metaDelegateByType(e2, user2, user3, PROPOSITION_POWER(), deadline, v, r, s);

    address propositionDelegateOfUser1AfterMetaDelegateByType = getPropositionDelegate(user1);
    assert propositionDelegateOfUser1AfterMetaDelegateByType != user3, "delegate not transitive";

}

rule delegationAwareBalanceChange() {
   
    address user1;
    address user2;
    env e;
    method f;
    calldataarg args;

    require user1 != user2;

    mathint balanceOfUser1Before = balanceOf(user1);
    mathint balanceOfUser2Before = balanceOf(user2);
    mathint delegatedVotingBalanceOfUser1Before = getDelegatedVotingBalance(user1);
    mathint delegatedVotingBalanceOfUser2Before = getDelegatedVotingBalance(user2);
    mathint delegatedPropositionBalanceOfUser1Before = getDelegatedPropositionBalance(user1);
    mathint delegatedPropositionBalanceOfUser2Before = getDelegatedPropositionBalance(user2);

    f(e, args);

    mathint balanceOfUser1After = balanceOf(user1);
    mathint balanceOfUser2After = balanceOf(user2);
    mathint delegatedVotingBalanceOfUser1After = getDelegatedVotingBalance(user1);
    mathint delegatedVotingBalanceOfUser2After = getDelegatedVotingBalance(user2);
    mathint delegatedPropositionBalanceOfUser1After = getDelegatedPropositionBalance(user1);
    mathint delegatedPropositionBalanceOfUser2After = getDelegatedPropositionBalance(user2);

    assert (
        balanceOfUser1Before == balanceOfUser1After || 
        balanceOfUser2Before == balanceOfUser2After || 
        (
            balanceOfUser1Before != balanceOfUser1After && 
            balanceOfUser2Before != balanceOfUser2After && 
            balanceOfUser1Before + balanceOfUser2Before == balanceOfUser1After + balanceOfUser2After
        )
    ), "integrity of balance";

    assert f.selector != transferFrom(address,address,uint256).selector && 
    f.selector != transfer(address,uint256).selector => (
        delegatedVotingBalanceOfUser1Before == delegatedVotingBalanceOfUser1After || 
        delegatedVotingBalanceOfUser2Before == delegatedVotingBalanceOfUser2After || 
        (
            delegatedVotingBalanceOfUser1Before != delegatedVotingBalanceOfUser1After && 
            delegatedVotingBalanceOfUser2Before != delegatedVotingBalanceOfUser2After && 
            delegatedVotingBalanceOfUser1Before + delegatedVotingBalanceOfUser2Before == delegatedVotingBalanceOfUser1After + delegatedVotingBalanceOfUser2After
        )
    ), "integrity of delegated balance";

    assert f.selector != transferFrom(address,address,uint256).selector && 
    f.selector != transfer(address,uint256).selector => (
        delegatedPropositionBalanceOfUser1Before == delegatedPropositionBalanceOfUser1After || 
        delegatedPropositionBalanceOfUser2Before == delegatedPropositionBalanceOfUser2After || 
        (
            delegatedPropositionBalanceOfUser1Before != delegatedPropositionBalanceOfUser1After && 
            delegatedPropositionBalanceOfUser2Before != delegatedPropositionBalanceOfUser2After && 
            delegatedPropositionBalanceOfUser1Before + delegatedPropositionBalanceOfUser2Before == delegatedPropositionBalanceOfUser1After + delegatedPropositionBalanceOfUser2After
        )
    ), "integrity of proposition balance";

}

rule powerEqualsToBalanceCondition() {
    env e;
    address user;
    uint256 balanceOfUser = balanceOf(user);

    require balanceOfUser > 0;

    uint256 votingPowerOfUser = getPowerCurrent(user, VOTING_POWER());
    uint256 propositionPowerOfUser = getPowerCurrent(user, PROPOSITION_POWER());
    uint256 delegatedVotingBalanceOfUser = getDelegatedVotingBalance(user);
    uint256 delegatedPropositionBalanceOfUser = getDelegatedPropositionBalance(user);
    address votingDelegateOfUser = getVotingDelegate(user);
    address propositionDelegateOfUser = getPropositionDelegate(user);
    
    require getDelegationState(user) == NO_DELEGATION();

    assert delegatedVotingBalanceOfUser == 0 && votingDelegateOfUser == 0 =>
    votingPowerOfUser == balanceOfUser,
    "voting power same as balance condition";

    assert delegatedPropositionBalanceOfUser == 0 && propositionDelegateOfUser == 0 =>
    propositionPowerOfUser == balanceOfUser,
    "proposition power same as balance condiiton";
    
}

rule delegateDoesNotInterfereWithAnotherUsers() {
    env e;
    address delegatee;
    address anotherUser;

    require e.msg.sender != delegatee && e.msg.sender != anotherUser && delegatee != anotherUser;
    require delegatee != 0;

    address votingDelegateBefore = getVotingDelegate(anotherUser);
    address propositionDelegateBefore = getPropositionDelegate(anotherUser);
    mathint delegatedVotingBalanceBefore = getDelegatedVotingBalance(anotherUser);
    mathint delegatedPropositionBalanceBefore = getDelegatedPropositionBalance(anotherUser);
    mathint balanceBefore = getBalance(anotherUser);

    require getVotingDelegate(e.msg.sender) != anotherUser && getPropositionDelegate(e.msg.sender) != anotherUser;

    delegate(e, delegatee);

    address votingDelegateAfter = getVotingDelegate(anotherUser);
    address propositionDelegateAfter = getPropositionDelegate(anotherUser);
    mathint delegatedVotingBalanceAfter = getDelegatedVotingBalance(anotherUser);
    mathint delegatedPropositionBalanceAfter = getDelegatedPropositionBalance(anotherUser);
    mathint balanceAfter = getBalance(anotherUser);

    assert votingDelegateBefore == votingDelegateAfter, "voting delegate of another user should not change";
    assert propositionDelegateBefore == propositionDelegateAfter, "proposition delegate of another user should not change";
    assert delegatedVotingBalanceBefore == delegatedVotingBalanceAfter, "delegated voting balance of another user should not change";
    assert delegatedPropositionBalanceBefore == delegatedPropositionBalanceAfter, "delegated proposition balance of another user should not change";
    assert balanceBefore == balanceAfter, "balance of another user should not change";
}  
/**
    Account1 is delegating power to delegatee1, account2 is delegating power to delegatee2
    Checking here for VOTING_POWER(), same will hold for proposition power
*/
rule transferEffectOnState() {
    env e;
    address user1;
    address user2;
    address delegatee1;
    address delegatee2;
    uint256 amount;

    require e.msg.sender == user1;
    require user1 != user2;
    require user1 != delegatee1 && user1 != delegatee2;
    require user2 != delegatee1 && user2 != delegatee2;
    require getDelegatedVotingBalance(user1) == 0 && getDelegatedVotingBalance(user2) == 0;
    require getDelegationState(user1) == VOTING_DELEGATED() && getDelegationState(user2) == VOTING_DELEGATED();

    address votingDelegateeOfUser1 = getVotingDelegate(user1);
    address votingDelegateeOfUser2 = getVotingDelegate(user2);

    require votingDelegateeOfUser1 == delegatee1 && votingDelegateeOfUser2 == delegatee2;

    require delegatee1 != delegatee2;

    mathint votingPowerOfUser1Before = getPowerCurrent(user1, VOTING_POWER());
    mathint votingPowerOfDelegatee1Before = getPowerCurrent(delegatee1, VOTING_POWER());
    uint256 balanceOfUser1Before = balanceOf(user1);

    mathint votingPowerOfUser2Before = getPowerCurrent(user2, VOTING_POWER());
    mathint votingPowerOfDelegatee2Before = getPowerCurrent(delegatee2, VOTING_POWER());
    uint256 balanceOfUser2Before = balanceOf(user2);

    transfer(e, user2, amount);

    mathint votingPowerOfUser1After = getPowerCurrent(user1, VOTING_POWER());
    mathint votingPowerOfDelegatee1After = getPowerCurrent(delegatee1, VOTING_POWER());
    uint256 balanceOfUser1After = balanceOf(user1);

    mathint votingPowerOfUser2After = getPowerCurrent(user2, VOTING_POWER());
    mathint votingPowerOfDelegatee2After = getPowerCurrent(delegatee2, VOTING_POWER());
    uint256 balanceOfUser2After = balanceOf(user2);

    assert votingPowerOfUser1Before == votingPowerOfUser1After && votingPowerOfUser1Before == 0;
    assert votingPowerOfUser2Before == votingPowerOfUser2After && votingPowerOfUser2Before == 0;

    assert votingPowerOfDelegatee1After <= votingPowerOfDelegatee1Before;

    assert votingPowerOfDelegatee2After >= votingPowerOfDelegatee2Before;

}

rule otherUserCanOnlyChangeDelegateThroughMetaFunctions() {
    env e;
    address user;
    method f;
    calldataarg args;

    address votingDelegateOfUserBefore = getVotingDelegate(user);
    address propositionDelegateOfUserBefore = getPropositionDelegate(user);

    f(e, args);

    address votingDelegateOfUserAfter = getVotingDelegate(user);
    address propositionDelegateOfUserAfter = getPropositionDelegate(user);

    assert (votingDelegateOfUserBefore != votingDelegateOfUserAfter || 
    propositionDelegateOfUserBefore != propositionDelegateOfUserAfter
    ) && (
        e.msg.sender != user
    ) => (
        f.selector == metaDelegate(address,address,uint256,uint8,bytes32,bytes32).selector ||
        f.selector == metaDelegateByType(address,address,uint8,uint256,uint8,bytes32,bytes32).selector
    ), "Only meta function can change delegate of another users";

}
/**
    Property verification: Account1 not delegating power to anybody, account2 is delegating power to delegatee2 
    checking for delegated voting but same will hold for proposition
*/
rule transferEffectOnPower() {
    env e;
    address user1;
    address user2;
    address delegatee1;
    address delegatee2;
    uint256 amount;

    require e.msg.sender == user1;
    require user1 != user2;
    require user1 != delegatee1 && user1 != delegatee2;
    require user2 != delegatee1 && user2 != delegatee2;
    require getDelegatedVotingBalance(user1) == 0 && getDelegatedVotingBalance(user2) == 0;
    require getDelegationState(user1) == NO_DELEGATION() && getDelegationState(user2) == VOTING_DELEGATED();

    address votingDelegateeOfUser1 = getVotingDelegate(user1);
    address votingDelegateeOfUser2 = getVotingDelegate(user2);

    require votingDelegateeOfUser1 == 0 && votingDelegateeOfUser2 == delegatee2;

    require delegatee1 != delegatee2;

    mathint user1PowerBefore = getPowerCurrent(user1, VOTING_POWER());
    mathint user2PowerBefore = getPowerCurrent(user2, VOTING_POWER());
    mathint delegatee2PowerBefore = getPowerCurrent(delegatee2, VOTING_POWER());

    transfer(e, user2, amount);

    mathint user1PowerAfter = getPowerCurrent(user1, VOTING_POWER());
    mathint user2PowerAfter = getPowerCurrent(user2, VOTING_POWER());
    mathint delegatee2PowerAfter = getPowerCurrent(delegatee2, VOTING_POWER());

    assert user1PowerAfter == user1PowerBefore - amount;
    assert user2PowerAfter == user2PowerBefore && user2PowerAfter == 0;
    assert delegatee2PowerAfter >= delegatee2PowerBefore;

}

rule stateChangeOfDelegation() {
    env e;
    address user;
    method f;
    calldataarg args;

    uint8 delegationStateBefore = getDelegationState(user);

    f(e, args);

    uint8 delegationStateAfter = getDelegationState(user);

    require delegationStateBefore != delegationStateAfter;

    assert f.selector == delegate(address).selector || 
    f.selector == delegateByType(address,uint8).selector || 
    f.selector == metaDelegate(address,address,uint256,uint8,bytes32,bytes32).selector || 
    f.selector == metaDelegateByType(address,address,uint8,uint256,uint8,bytes32,bytes32).selector;
}

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

/**

    Testing correctness of delegate(). An example of a unit test

*/

// rule delegateCorrectness(address bob) {
//     env e;
//     // delegate not to self or to zero
//     require bob != e.msg.sender && bob != 0;

//     uint256 bobDelegatedBalance = getDelegatedVotingBalance(bob);
//     // avoid unrealistic delegated balance
//     require(bobDelegatedBalance < MAX_DELEGATED_BALANCE());
    
//     // verify that the sender doesn't already delegate to bob
//     address delegateBefore = getVotingDelegate(e.msg.sender);
//     require delegateBefore != bob;

//     uint256 bobVotingPowerBefore = getPowerCurrent(bob, VOTING_POWER());
//     uint256 delegatorBalance = balanceOf(e.msg.sender);

//     delegate(e, bob);

//     // test the delegate indeed has changed to bob
//     address delegateAfter = getVotingDelegate(e.msg.sender);
//     assert delegateAfter == bob;

//     // test the delegate's new voting power
//     uint256 bobVotingPowerAfter = getPowerCurrent(bob, VOTING_POWER());
//     assert bobVotingPowerAfter == bobVotingPowerBefore + normalize(delegatorBalance);
// }

// /**

//     Verify that only delegate functions can change someone's delegate.
//     An example for a parametric rule.

// */

// rule votingDelegateChanges(address alice, method f) {
//     env e;
//     calldataarg args;

//     address aliceDelegateBefore = getVotingDelegate(alice);

//     f(e, args);

//     address aliceDelegateAfter = getVotingDelegate(alice);

//     // only these four function may change the delegate of an address
//     assert aliceDelegateAfter != aliceDelegateBefore =>
//         f.selector == delegate(address).selector || 
//         f.selector == delegateByType(address,uint8).selector ||
//         f.selector == metaDelegate(address,address,uint256,uint8,bytes32,bytes32).selector ||
//         f.selector == metaDelegateByType(address,address,uint8,uint256,uint8,bytes32,bytes32).selector;
// }

/**

    A ghost variable that tracks the sum of all addresses' balances

*/
// ghost mathint sumBalances {
//     init_state axiom sumBalances == 0;
// }

// // /**

// //     This hook updates the sumBalances ghost whenever any address balance is updated

// // */