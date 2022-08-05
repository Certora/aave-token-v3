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

rule propositionDelegateChanges(address alice, method f) {
    env e;
    calldataarg args;

    address aliceDelegateBefore = getPropositionDelegate(alice);

    f(e, args);

    address aliceDelegateAfter = getPropositionDelegate(alice);

    // only these four function may change the delegate of an address
    assert aliceDelegateAfter != aliceDelegateBefore =>
        f.selector == delegate(address).selector || 
        f.selector == delegateByType(address,uint8).selector ||
        f.selector == metaDelegate(address,address,uint256,uint8,bytes32,bytes32).selector ||
        f.selector == metaDelegateByType(address,address,uint8,uint256,uint8,bytes32,bytes32).selector;
}

rule powerChanges(address alice, method f) {
    env e;
    calldataarg args;

    uint8 type;
    require type <= 1;
    uint256 powerBefore = getPowerCurrent(alice, type);

    f(e, args);

    uint256 powerAfter = getPowerCurrent(alice, type);

    assert powerBefore != powerAfter =>
        f.selector == delegate(address).selector ||
        f.selector == delegateByType(address, uint8).selector ||
        f.selector == metaDelegate(address, address, uint256, uint8, bytes32, bytes32).selector ||
        f.selector == metaDelegateByType(address, address, uint8, uint256, uint8, bytes32, bytes32).selector ||
        f.selector == transfer(address, uint256).selector ||
        f.selector == transferFrom(address, address, uint256).selector ||
        // For some reason this function is public
        f.selector == _governancePowerTransferByType(uint104, uint104, address, uint8).selector;
}

rule delegateIndependence(method f) {
    env e;

    uint8 type;
    require type <= 1;

    address delegateBefore = type == 1 ? getPropositionDelegate(e.msg.sender) : getVotingDelegate(e.msg.sender);

    delegateByType(e, _, 1 - type);

    address delegateAfter = type == 1 ? getPropositionDelegate(e.msg.sender) : getVotingDelegate(e.msg.sender);

    assert delegateBefore == delegateAfter;
}

rule metaDelegateIndependence(method f) {
    env e;
    address addr;

    uint8 type;
    require type <= 1;

    address delegateBefore = type == 1 ? getPropositionDelegate(addr) : getVotingDelegate(addr);

    metaDelegateByType(e,   addr, _, 1 - type, _, _, _, _);

    address delegateAfter = type == 1 ? getPropositionDelegate(addr) : getVotingDelegate(addr);

    assert delegateBefore == delegateAfter;
}

rule powerChangesOnTransfer() {
    env e;
    address bob;
    require e.msg.sender != bob;
    uint256 amount;

    uint8 type;
    require type <= 1;
    uint256 powerBefore = getPowerCurrent(e.msg.sender, type);
    uint256 bobPowerBefore = getPowerCurrent(bob, type);
    // Assert balances are sane to avoid impossible corner cases
    require(balanceOf(e.msg.sender) < MAX_DELEGATED_BALANCE());
    require(getDelegatedVotingBalance(e.msg.sender) < MAX_DELEGATED_BALANCE());
    require(getDelegatedPropositionBalance(e.msg.sender) < MAX_DELEGATED_BALANCE());
    require(balanceOf(bob) < MAX_DELEGATED_BALANCE());
    require(getDelegatedVotingBalance(bob) < MAX_DELEGATED_BALANCE());
    require(getDelegatedPropositionBalance(bob) < MAX_DELEGATED_BALANCE());

    transfer(e, bob, amount);

    uint256 powerAfter = getPowerCurrent(e.msg.sender, type);
    uint256 bobPowerAfter = getPowerCurrent(bob, type);

    assert powerAfter == powerBefore - amount
        && bobPowerAfter == bobPowerBefore + amount;
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