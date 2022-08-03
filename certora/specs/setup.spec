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
    getDelegationState(address a) returns (uint8) envfree
    getPropositionDelegate(address user) returns (address) envfree
    getNonce(address) returns (uint256) envfree
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

invariant addressZeroNoPower()
  getPowerCurrent(0, VOTING_POWER()) == 0 && getPowerCurrent(0, PROPOSITION_POWER()) == 0 && balanceOf(0) == 0

rule delegateAnddelegatebytypeComparison {
  storage initialState = lastStorage;
  env e;
  address alice;
  require alice != e.msg.sender && alice != 0;
  delegate(e, alice) at initialState;
  uint256 aliceVotingPowerDelegate = getPowerCurrent(alice, VOTING_POWER());
  uint256 alicePropositionPowerDelegate = getPowerCurrent(alice, PROPOSITION_POWER());
  uint72 aliceVotingBalanceDelegate=getDelegatedVotingBalance(alice);
  uint72 alicePropositionBalanceDelegate=getDelegatedPropositionBalance(alice);
  delegateByType(e, alice, VOTING_POWER()) at initialState;
  delegateByType(e, alice, PROPOSITION_POWER());
  uint256 aliceVotingPowerDelegateByType = getPowerCurrent(alice, VOTING_POWER());
  uint256 alicePropositionPowerDelegateByType = getPowerCurrent(alice, PROPOSITION_POWER());
  uint72 aliceVotingBalanceDelegateByType=getDelegatedVotingBalance(alice);
  uint72 alicePropositionBalanceDelegateByType=getDelegatedPropositionBalance(alice);
  assert aliceVotingPowerDelegate==aliceVotingPowerDelegateByType;
  assert alicePropositionPowerDelegate==alicePropositionPowerDelegateByType;
  assert aliceVotingBalanceDelegate==aliceVotingBalanceDelegateByType;
  assert alicePropositionBalanceDelegate==alicePropositionBalanceDelegateByType;
}

rule delegateByTypeCorrectness() {
    env e;
    address user;
    require user != e.msg.sender && user != 0;

    uint256 userDelegatedBalance = getDelegatedVotingBalance(user);    
    address delegateBefore = getVotingDelegate(e.msg.sender);
    require delegateBefore != user;

    uint256 userVotingPowerBefore = getPowerCurrent(user, VOTING_POWER());
    uint256 delegatorBalance = balanceOf(e.msg.sender);

    delegateByType(e, user, VOTING_POWER());

    address delegateAfter = getVotingDelegate(e.msg.sender);
    assert delegateAfter == user;

    uint256 userVotingPowerAfter = getPowerCurrent(user, VOTING_POWER());
    assert userVotingPowerAfter == userVotingPowerBefore + normalize(delegatorBalance);
}

rule metaDelegateCorrectness() {
    env e;
    address delegator;
    address delegatee;
    uint256 deadline;
    uint8 v;
    bytes32 r;
    bytes32 s;
    require e.block.timestamp > deadline;
    metaDelegate@withrevert(e, delegator, delegatee, deadline, v, r, s);
    assert lastReverted;
}

rule stateChangeFunctions() {
  env e;
  address user;
  method f;
  calldataarg args;
  uint8 stateBefore = getDelegationState(user);
  f(e, args);
  uint8 stateAfter = getDelegationState(user);
  require stateBefore != stateAfter;
  assert f.selector == delegate(address).selector ||
  f.selector == delegateByType(address,uint8).selector ||
  f.selector == metaDelegate(address,address,uint256,uint8,bytes32,bytes32).selector ||
  f.selector == metaDelegateByType(address,address,uint8,uint256,uint8,bytes32,bytes32).selector;
}

rule nonceChangeFunctions() {
  env e;
  calldataarg args;
  method f;
  address sender = e.msg.sender;
  uint256 nonceBefore = getNonce(sender);
  f(e, args);
  uint256 nonceAfter = getNonce(sender);
  assert nonceBefore != nonceAfter =>
      f.selector == metaDelegate(address,address,uint256,uint8,bytes32,bytes32).selector ||
      f.selector == metaDelegateByType(address,address,uint8,uint256,uint8,bytes32,bytes32).selector ||
      f.selector == permit(address,address,uint256,uint256,uint8,bytes32,bytes32).selector;
}

rule balanceChangeFunctions() {
  env e;
  address alice;
  calldataarg args;
  method f;
  uint256 balanceBefore = balanceOf(alice);
  f(e, args);
  uint256 balanceAfter = balanceOf(alice);
  assert balanceAfter != balanceBefore =>
    f.selector == transfer(address,uint256).selector ||
    f.selector == transferFrom(address,address,uint256).selector;
}

rule delegationIndependentOfEachOther() {

    env e;
    address alice;
    address bob;

    storage initialState = lastStorage;
    address votingDelegateBefore = getVotingDelegate(alice);
    delegateByType(e, bob, PROPOSITION_POWER());
    address votingDelegateAfter = getVotingDelegate(alice);

    address propositionDelegateBefore = getPropositionDelegate(alice) at initialState;
    delegateByType(e, bob, VOTING_POWER());
    address propositionDelegateAfter = getPropositionDelegate(alice);

    assert votingDelegateBefore == votingDelegateAfter;
    assert propositionDelegateBefore == propositionDelegateAfter;
}

rule nonDelegatingAndNotBeignDelegatedUserPowerEqBalance(){
    address user;
    require getPropositionDelegate(user) == 0; 
    require getVotingDelegate(user) == 0;
    require getDelegatedPropositionBalance(user) == 0;
    require getDelegatedVotingBalance(user) == 0;
    require getDelegationState(user) == 0;

    assert getPowerCurrent(user, VOTING_POWER()) == balanceOf(user) && getPowerCurrent(user, PROPOSITION_POWER()) == balanceOf(user);
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

invariant totalSupplyEqualsBalances()
    sumBalances == totalSupply()