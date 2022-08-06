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
    getDelegatedPowerByType(address user, uint8 delegationType) returns (uint256) envfree
    getDelegationState(address user) returns (uint8) envfree
}

/**

    Constants

*/
// GovernancyType enum from the token contract
definition VOTING_POWER() returns uint8 = 0;
definition PROPOSITION_POWER() returns uint8 = 1;

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
    The sum of all delegated voting balance must be less or equal to the totalSupply
*/
ghost mathint sumDelegatedVotingBalances {
    init_state axiom sumDelegatedVotingBalances == 0;
}


hook Sstore _balances[KEY address user].delegatedVotingBalance uint72 new_delegated_voting_balance
    (uint72 old_delegated_voting_balance) STORAGE {
        sumDelegatedVotingBalances = sumDelegatedVotingBalances - to_mathint(old_delegated_voting_balance) + to_mathint(new_delegated_voting_balance);
    }

/**
    Check that there is no way to increase or decrease the totalSupply
*/
rule nothingAffectsTotalSupply(env e, address user, method f){
    uint256 totalSupplyBefore = totalSupply();

    calldataarg args;
    f(e, args);

    assert totalSupply() == totalSupplyBefore;
}

/**
    It is not possible to delegate to the 0 address, the only voting power it has is its balance
*/
invariant zeroAddressCanNotBeDelegatedTo()
    getDelegatedVotingBalance(0) == balanceOf(0) && getDelegatedPropositionBalance(0) == balanceOf(0)


/**
   Alice can only change Bobs delegate through a valid meta transaction
*/
rule anotherUserCanOnlyChangeDelegateThroughMeta(env e, address user, method f) {
    address votingDelegateBefore = getVotingDelegate(user);
    address propositionDelegateAfter = getPropositionDelegate(user);

    calldataarg args;

    f(e, args);

    // If the delegate changed it must through a meta tx (or it was the user themselves who updated it)
    assert (
        votingDelegateBefore != getVotingDelegate(user) ||
        propositionDelegateAfter != getPropositionDelegate(user)
    ) && (
        f.selector != metaDelegateByType(address,address,uint8,uint256,uint8,bytes32,bytes32).selector &&
        f.selector != metaDelegate(address,address,uint256,uint8,bytes32,bytes32).selector
    )=> e.msg.sender == user;
}

/**
    From the properties.md
    If an account is not receiving delegation of power (one type) from anybody,
    and that account is not delegating that power to anybody, the power of that account must be equal to its AAVE balance.
*/
rule nonDelegatingUserPowerEqBalance(env e, bool delegateToSelf){
    enforceValidUserState(e.msg.sender);
    
    // User has no voting power being delegated to them
    require getPowerCurrent(e.msg.sender, VOTING_POWER()) == 0 && 
        getPowerCurrent(e.msg.sender, PROPOSITION_POWER()) == 0;

    // User stops delegating both types of power
    // either delegate to self directly or delegate to 0 address
    delegate(e, delegateToSelf ? e.msg.sender : 0);
    
    // Power of that account must be equal to its AAVE balance.
    assert getPowerCurrent(e.msg.sender, VOTING_POWER()) == getBalance(e.msg.sender) &&
             getPowerCurrent(e.msg.sender, PROPOSITION_POWER()) == getBalance(e.msg.sender);
}

/**
    This invariant check if the  result of `getPowerCurrent` is equal to the amount being delegated + the users balance (if they are not delegating)
*/
invariant correctnessOfgetPowerCurrent(address user)
    getDelegatedPowerByType(user, VOTING_POWER()) // The amount delegated to this user
        +
    (getDelegatingVoting(user) == false ? getBalance(user) : 0) // if the user is self-delegating then the users balance should be added to the total
        ==
    getPowerCurrent(user, VOTING_POWER()) // is equal to the amount the method should return


/**
    The prover might use a starting state where `delegationState` is in an unreachable state
    ex. `delegationState` set to `FULL_POWER_DELEGATED` but no delegate address set
*/
function enforceValidUserState(address user){
    require getVotingDelegate(user) == 0 => getDelegatingVoting(user) == false;
    require getPropositionDelegate(user) == 0 => getDelegatingProposition(user) == false;
}

