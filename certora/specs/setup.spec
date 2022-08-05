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
    Integrity of delegate(address delegatee)
    Adds msg.sender’s balance to delegatee voting & proposing power
    Updates voting delegate of msg.sender 
*/

rule CheckIntegrityOfDelegateeIsUpdated() {
    env e;
    address receiver;

    uint256 balance_of_voting_power_of_sender = getPowerCurrent(e.msg.sender, VOTING_POWER());
    uint256 delegator_balance_before = balanceOf(e.msg.sender);
    address current_delegatee_before = getDelegateeByType(e, e.msg.sender, VOTING_POWER());

    require receiver != e.msg.sender && receiver != 0;
    delegate(e, receiver);

    uint256 balance_of_voting_power_of_receiver = getPowerCurrent(receiver, VOTING_POWER());
    uint256 delegator_balance_after = balanceOf(e.msg.sender);
    address current_delegatee_after = getDelegateeByType(e, e.msg.sender, VOTING_POWER());

    assert current_delegatee_after == receiver;
}

/**
    An account cannot delegate power that has been delegated to it from another account 
*/

rule CannotDelegatePowerGivenBySomeOne {
    env e;
    address delegator2;
    address delegator3;
    uint256 deadline;
    uint8 v;
    bytes32 r;
    bytes32 s;

    require delegator2 != e.msg.sender && delegator2 != 0;
    require delegator3 != delegator2 && delegator3 != 0;

    uint256 balance_of_voting_power_of_sender = getPowerCurrent(e.msg.sender, VOTING_POWER());
    uint256 balance_of_delegator2_before = balanceOf(delegator2);
    uint256 balance_of_voting_power_of_delegator2_before = getPowerCurrent(delegator2, VOTING_POWER());
    uint256 delegator_balance_before = balanceOf(e.msg.sender); 
    delegate(e, delegator2);

    uint256 balance_of_voting_power_of_delegator2 = getPowerCurrent(delegator2, VOTING_POWER());
    env e1;
    metaDelegateByType(e1, delegator2, delegator3, VOTING_POWER(), deadline, v, r, s);
    uint256 balance_of_voting_power_of_delegator3 = getPowerCurrent(delegator3, VOTING_POWER());

    assert balance_of_voting_power_of_delegator2_before == balance_of_voting_power_of_delegator3;
}

/**
    If an account is delegating, it needs to delegate full power and not the portion of it
*/

rule ShouldBeAbleTransferFullPower {
    env e1;
    address receiver;

    require receiver != e1.msg.sender && receiver != 0;

    uint256 balance_of_voting_power_of_sender = getPowerCurrent(e1.msg.sender, VOTING_POWER());
    delegate(e1, receiver);
    uint256 balance_of_voting_power_of_receiver = getPowerCurrent(receiver, VOTING_POWER());
    uint256 balance_of_receiver = balanceOf(receiver);

    assert balance_of_voting_power_of_sender == balance_of_voting_power_of_receiver - balance_of_receiver;
}

/**
    User can delegate power only if his balance is > 0
*/

rule ShouldTransferPowerIfBalanceIsGreaterThanZero {
    env e1;
    address receiver;

    require receiver != e1.msg.sender && receiver != 0;
    require balanceOf(e1.msg.sender) > 0; 

    uint256 balance_of_voting_power_of_sender = getPowerCurrent(e1.msg.sender, VOTING_POWER());
    delegate(e1, receiver);
    uint256 balance_of_voting_power_of_receiver = getPowerCurrent(receiver, VOTING_POWER());
    uint256 balance_of_receiver = balanceOf(receiver);

    assert balance_of_voting_power_of_sender == balance_of_voting_power_of_receiver - balance_of_receiver;
}
