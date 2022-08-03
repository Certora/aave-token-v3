import "./setup.spec"

/**
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
**/
methods {
  getNotDelegating(address user) returns (bool) envfree
  getDelegatingPropositionOnly(address user) returns (bool) envfree
  getDelegatingVotingOnly(address user) returns (bool) envfree
  getFullDelegating(address user) returns (bool) envfree
}

/****************
 Helper Functions
****************/

/**
  Function to check if _addr has correct power, not delegated yet
  and has balance
**/
function initializeAddressChecks(address _addr) {
  uint256 delegatedBalanceVoting = getDelegatedVotingBalance(_addr);
  uint256 delegatedBalanceProposition = getDelegatedPropositionBalance(_addr);
  // avoid unrealistic delegated balance
  require delegatedBalanceVoting < MAX_DELEGATED_BALANCE();
  require delegatedBalanceProposition < MAX_DELEGATED_BALANCE();

  address delegateVoting = getVotingDelegate(_addr);
  address delegateProposition = getPropositionDelegate(_addr);
  // not delegated yet
  require delegateVoting == 0 && delegateProposition == 0;

  uint256 addrBalance = balanceOf(_addr);
  require addrBalance > 0;
}

/**
  Function to check if _addr has correct power, not delegated yet
  and has no balance
**/
function initializeAddressChecksWithoutBalance(address _addr) {
  uint256 delegatedBalanceVoting = getDelegatedVotingBalance(_addr);
  uint256 delegatedBalanceProposition = getDelegatedPropositionBalance(_addr);
  // avoid unrealistic delegated balance
  require delegatedBalanceVoting < MAX_DELEGATED_BALANCE();
  require delegatedBalanceProposition < MAX_DELEGATED_BALANCE();

  address delegateVoting = getVotingDelegate(_addr);
  address delegateProposition = getPropositionDelegate(_addr);
  // not delegated yet
  require delegateVoting == 0 && delegateProposition == 0;

  uint256 addrBalance = balanceOf(_addr);
  require addrBalance == 0;
}

/******
 Rules
******/

/**
    Verify if power update correctly
    when user delegate by voting or proposition
*/
rule delegateByTypeCorrectness {
  env e;
  address alice;
  uint8 randomPower;

  // pick a random type
  uint8 delegateType = randomPower % 2 == 0 ? VOTING_POWER() : PROPOSITION_POWER();

  // delegate not to self or to zero
  require alice != e.msg.sender && alice != 0;

  initializeAddressChecks(e.msg.sender);
  initializeAddressChecks(alice);

  // get voting and proposition power before delegateByType
  uint256 aliceVotingPowerBefore = getPowerCurrent(alice, VOTING_POWER());
  uint256 alicePropositionPowerBefore = getPowerCurrent(alice, PROPOSITION_POWER());

  delegateByType(e, alice, delegateType);

  // get delegate new voting and proposition power
  uint256 aliceVotingPowerAfter = getPowerCurrent(alice, VOTING_POWER());
  uint256 alicePropositionPowerAfter = getPowerCurrent(alice, PROPOSITION_POWER());

  uint256 delegatorBalance = balanceOf(e.msg.sender);

  if (delegateType == VOTING_POWER()){
    // test the delegate indeed has changed to alice
    address votingDelegate = getVotingDelegate(e.msg.sender);
    assert votingDelegate == alice, "Did not delegate to alice";

    assert aliceVotingPowerAfter == aliceVotingPowerBefore + normalize(delegatorBalance) => alicePropositionPowerAfter == alicePropositionPowerBefore, "Invalid Power";
  } else {
    // test the delegate indeed has changed to alice
    address propositionDelegate = getPropositionDelegate(e.msg.sender);
    assert propositionDelegate == alice, "Did not delegate to alice";

    assert alicePropositionPowerAfter == alicePropositionPowerBefore + normalize(delegatorBalance) => aliceVotingPowerAfter == aliceVotingPowerBefore, "Invalid Power";
  }
}

/**
  Verify if delegate to itself or zero address
  works properly
**/
rule delegateToZeroOrItselfAddresses {
  env e;
  address alice;

  // delegate to self or to zero
  require alice == e.msg.sender || alice == 0;

  initializeAddressChecks(e.msg.sender);
  initializeAddressChecks(alice);

  // get voting and proposition power before delegate
  uint256 aliceVotingPowerBefore = getPowerCurrent(alice, VOTING_POWER());
  uint256 alicePropositionPowerBefore = getPowerCurrent(alice, PROPOSITION_POWER());

  // don't have delegate it power yet
  require getDelegateeByType(e, alice, PROPOSITION_POWER()) == 0;

  delegate(e, alice);

  // test the delegate's new voting power
  uint256 aliceVotingPowerAfter = getPowerCurrent(alice, VOTING_POWER());
  uint256 alicePropositionPowerAfter = getPowerCurrent(alice, PROPOSITION_POWER());

  uint256 delegatorBalance = balanceOf(e.msg.sender);

  assert aliceVotingPowerBefore == aliceVotingPowerAfter => alicePropositionPowerBefore == alicePropositionPowerAfter, "Power Changed";
}

/**
  Check if there the power changes to another user
  when changing the delegation from alice to bob
**/
rule delegateChangeToAnotherAddress {
  env e;
  address alice;
  address bob;
  uint8 randomPower;

  // pick a random type
  uint8 delegateType = randomPower % 2 == 0 ? VOTING_POWER() : PROPOSITION_POWER();

  // delegate not to self or to zero
  // bob must be different from alice
  require alice != e.msg.sender && alice != 0;
  require bob != e.msg.sender && bob != 0 && bob != alice;

  initializeAddressChecks(e.msg.sender);
  initializeAddressChecks(alice);
  initializeAddressChecks(bob);

  // get voting and proposition power before
  uint256 aliceVotingPowerBefore = getPowerCurrent(alice, VOTING_POWER());
  uint256 alicePropositionPowerBefore = getPowerCurrent(alice, PROPOSITION_POWER());
  uint256 bobVotingPowerBefore = getPowerCurrent(bob, VOTING_POWER());
  uint256 bobPropositionPowerBefore = getPowerCurrent(bob, PROPOSITION_POWER());


  delegateByType(e, alice, delegateType);
  delegateByType(e, bob, delegateType);

  // get new voting and proposition power
  uint256 aliceVotingPowerAfter = getPowerCurrent(alice, VOTING_POWER());
  uint256 alicePropositionPowerAfter = getPowerCurrent(alice, PROPOSITION_POWER());
  uint256 bobVotingPowerAfter = getPowerCurrent(bob, VOTING_POWER());
  uint256 bobPropositionPowerAfter = getPowerCurrent(bob, PROPOSITION_POWER());

  uint256 delegatorBalance = balanceOf(e.msg.sender);

  if (delegateType == VOTING_POWER()){
    // test the delegate indeed has changed to alice
    address votingDelegate = getVotingDelegate(e.msg.sender);
    assert votingDelegate == bob, "Did not delegate to bob";

    assert aliceVotingPowerAfter == aliceVotingPowerBefore => alicePropositionPowerAfter == alicePropositionPowerBefore, "Invalid Alice Power";
    assert bobVotingPowerAfter == bobVotingPowerBefore + normalize(delegatorBalance) => bobPropositionPowerAfter == bobPropositionPowerBefore, "Invalid Bob Power";
  } else {
    // test the delegate indeed has changed to alice
    address propositionDelegate = getPropositionDelegate(e.msg.sender);
    assert propositionDelegate == bob, "Did not delegate to bob";

    assert alicePropositionPowerAfter == alicePropositionPowerBefore + normalize(delegatorBalance) => aliceVotingPowerAfter == aliceVotingPowerBefore, "Invalid Alice Power";
    assert bobPropositionPowerAfter == bobPropositionPowerBefore + normalize(delegatorBalance) => bobVotingPowerAfter == bobVotingPowerBefore, "Invalid Bob Power";
  }
}

/**
  Verify if when delegating it's not using delegated power
**/
rule delegateNotUseDelegatedPower {
  env e;
  address alice;
  address bob;
  uint256 deadline;
  uint8 v;
  bytes32 r;
  bytes32 s;

  // delegate not to self or to zero
  // and bob must be different from alice
  require alice != e.msg.sender && alice != 0;
  require bob != e.msg.sender && bob != 0 && bob != alice;

  initializeAddressChecks(e.msg.sender);
  initializeAddressChecks(alice);
  initializeAddressChecks(bob);

  // get voting and proposition power before
  uint256 aliceVotingPowerBefore = getPowerCurrent(alice, VOTING_POWER());
  uint256 alicePropositionPowerBefore = getPowerCurrent(alice, PROPOSITION_POWER());
  uint256 bobVotingPowerBefore = getPowerCurrent(bob, VOTING_POWER());
  uint256 bobPropositionPowerBefore = getPowerCurrent(bob, PROPOSITION_POWER());

  //msg.sender delegate power to alice
  delegate(e, alice);

  //alice delegate voting power to bob
  metaDelegateByType(e,alice,bob,VOTING_POWER(),deadline,v,r,s);

  //get new voting and proposition power
  uint256 aliceVotingPowerAfter = getPowerCurrent(alice, VOTING_POWER());
  uint256 alicePropositionPowerAfter = getPowerCurrent(alice, PROPOSITION_POWER());
  uint256 bobVotingPowerAfter = getPowerCurrent(bob, VOTING_POWER());
  uint256 bobPropositionPowerAfter = getPowerCurrent(bob, PROPOSITION_POWER());

  // test the delegate indeed has changed to alice
  address senderVotingDelegate = getVotingDelegate(e.msg.sender);
  assert senderVotingDelegate == alice, "Sender did not delegate to alice";

  address aliceVotingDelegate = getVotingDelegate(alice);
  assert aliceVotingDelegate == bob, "Alice did not delegate to bob";

  uint256 senderBalanceNormalized = normalize(balanceOf(e.msg.sender));
  uint256 aliceBalanceNormalized = normalize(balanceOf(alice));

  // test alice new power
  assert aliceVotingPowerAfter == aliceVotingPowerBefore + senderBalanceNormalized - aliceBalanceNormalized => alicePropositionPowerAfter == alicePropositionPowerBefore + senderBalanceNormalized, "Invalid Alice Power";

  // test bob new power
  assert bobVotingPowerAfter == bobVotingPowerBefore + aliceBalanceNormalized => bobPropositionPowerAfter == bobPropositionPowerBefore, "Invalid Bob Power";
}

/**
  Verify if delegating with zero balance
  not change the state and
  change voting/proposition delegatee
**/
rule delegateZeroBalanceNotChangeState {
  env e;
  address alice;

  // delegate not to self or to zero
  require alice != e.msg.sender && alice != 0;

  //require to state be no delegating
  require getNotDelegating(e.msg.sender);

  initializeAddressChecksWithoutBalance(e.msg.sender);
  initializeAddressChecks(alice);

  // get voting and proposition power before
  uint256 aliceVotingPowerBefore = getPowerCurrent(alice, VOTING_POWER());
  uint256 alicePropositionPowerBefore = getPowerCurrent(alice, PROPOSITION_POWER());

  delegate(e, alice);

  // get new voting and proposition power
  uint256 aliceVotingPowerAfter = getPowerCurrent(alice, VOTING_POWER());
  uint256 alicePropositionPowerAfter = getPowerCurrent(alice, PROPOSITION_POWER());

  // test the delegate indeed has changed to alice
  address votingDelegate = getVotingDelegate(e.msg.sender);
  address propositionDelegate = getPropositionDelegate(e.msg.sender);
  assert votingDelegate == alice => propositionDelegate == alice, "Did not delegate to alice";

  // check if alice power not changed (balance==0)
  assert aliceVotingPowerAfter == aliceVotingPowerBefore => alicePropositionPowerAfter == alicePropositionPowerBefore, "Invalid Alice Power";

  //the state of delegation shouldn't change
  assert getNotDelegating(e.msg.sender);
}

/**
  Verify if delegate and delegateByType have same logic
**/
rule compareDelegate {
  storage initialState = lastStorage;
  env e;
  address alice;

  // delegate not to self or to zero
  require alice != e.msg.sender && alice != 0;

  initializeAddressChecks(e.msg.sender);
  initializeAddressChecks(alice);

  delegate(e, alice) at initialState;

  //get power after delegate
  uint256 aliceVotingPowerDelegate = getPowerCurrent(alice, VOTING_POWER());
  uint256 alicePropositionPowerDelegate = getPowerCurrent(alice, PROPOSITION_POWER());

  delegateByType(e, alice, VOTING_POWER()) at initialState;
  delegateByType(e, alice, PROPOSITION_POWER());

  //get power after delegateByType
  uint256 aliceVotingPowerDelegateByType = getPowerCurrent(alice, VOTING_POWER());
  uint256 alicePropositionPowerDelegateByType = getPowerCurrent(alice, PROPOSITION_POWER());

  assert aliceVotingPowerDelegate == aliceVotingPowerDelegateByType => alicePropositionPowerDelegate == alicePropositionPowerDelegateByType, "Delegates are different";
}

/**
  Verify if user can revoke delegated power and
  change the state to not delegating
**/
rule revokeDelegatePower {
  env e;
  address alice;

  // delegate not to self or to zero
  require alice != e.msg.sender && alice != 0;

  initializeAddressChecks(e.msg.sender);
  initializeAddressChecks(alice);

  // get voting and proposition power before
  uint256 aliceVotingPowerBefore = getPowerCurrent(alice, VOTING_POWER());
  uint256 alicePropositionPowerBefore = getPowerCurrent(alice, PROPOSITION_POWER());

  delegate(e, alice);
  // revoke the delegated power
  delegate(e, 0);

  // get new voting and proposition power
  uint256 aliceVotingPowerAfter = getPowerCurrent(alice, VOTING_POWER());
  uint256 alicePropositionPowerAfter = getPowerCurrent(alice, PROPOSITION_POWER());

  assert aliceVotingPowerAfter == aliceVotingPowerBefore => alicePropositionPowerAfter == alicePropositionPowerBefore, "Invalid Alice Power";

  // check if revoked voting and proposition delegating
  address delegateVotingAfter = getVotingDelegate(e.msg.sender);
  address delegatePropositionAfter = getPropositionDelegate(e.msg.sender);
  assert delegateVotingAfter == 0 => delegatePropositionAfter == 0, "Did not revoke delegated power";

  assert getNotDelegating(e.msg.sender);
}

/**
  Verify what functions can change total power
**/
rule changeTotalPower {
    env e;
    address alice;
    calldataarg args;
    method f;

    initializeAddressChecks(e.msg.sender);
    initializeAddressChecks(alice);

    address delegateVotingBefore = getVotingDelegate(alice);
    address delegatePropositionBefore = getPropositionDelegate(alice);

    f(e, args);

    address delegateVotingAfter = getVotingDelegate(alice);
    address delegatePropositionAfter = getPropositionDelegate(alice);

    // only these functions may change the delegate power of an address
    assert delegateVotingBefore != delegateVotingAfter || delegatePropositionBefore != delegatePropositionAfter =>
        f.selector == delegate(address).selector ||
        f.selector == delegateByType(address,uint8).selector ||
        f.selector == metaDelegate(address,address,uint256,uint8,bytes32,bytes32).selector ||
        f.selector == metaDelegateByType(address,address,uint8,uint256,uint8,bytes32,bytes32).selector ||
        f.selector == transfer(address,uint256).selector ||
        f.selector == transferFrom(address,address,uint256).selector;
}


/**********
 Invariants
**********/

/**
  Verify if address zero has zero power
**/
invariant addressZeroPower()
  getPowerCurrent(0, VOTING_POWER()) == 0 &&
  getPowerCurrent(0, PROPOSITION_POWER()) == 0
  { preserved with (env e) { require e.msg.sender != 0; } }

/**
  Verify if voting/proposition power is calculated correctly
  considering the state change during the execution
  ps: it's "heavy" to run because of verifications
**/
invariant checkVotingPropositionPower(address alice)
  //If alice is delegating only voting
  //power of voting = delegated voting
  //power of proposition = balance + delegated proposition
  (getDelegatingVotingOnly(alice) &&
    getPowerCurrent(alice, VOTING_POWER()) == getDelegatedVotingBalance(alice) * DELEGATED_POWER_DIVIDER() &&
    getPowerCurrent(alice, PROPOSITION_POWER()) == balanceOf(alice) + getDelegatedPropositionBalance(alice) * DELEGATED_POWER_DIVIDER()
  ) ||
  //If alice is delegating only proposition
  //power of voting = balance + delegated voting
  //power of proposition = delegated proposition
  (getDelegatingPropositionOnly(alice) &&
    getPowerCurrent(alice, VOTING_POWER()) == balanceOf(alice) + getDelegatedVotingBalance(alice) * DELEGATED_POWER_DIVIDER() &&
    getPowerCurrent(alice, PROPOSITION_POWER()) == getDelegatedPropositionBalance(alice) * DELEGATED_POWER_DIVIDER()
  ) ||
  //If alice is full delegating
  //power of voting = delegated voting
  //power of proposition = delegated proposition
  (getFullDelegating(alice) &&
    getPowerCurrent(alice, VOTING_POWER()) == getDelegatedVotingBalance(alice) * DELEGATED_POWER_DIVIDER() &&
    getPowerCurrent(alice, PROPOSITION_POWER()) == getDelegatedPropositionBalance(alice) * DELEGATED_POWER_DIVIDER()
  ) ||
  //If alice is no delegating
  //power of voting = balance + delegated voting
  //power of proposition = balance + delegated proposition
  (getNotDelegating(alice) &&
    getPowerCurrent(alice, VOTING_POWER()) == balanceOf(alice) + getDelegatedVotingBalance(alice) * DELEGATED_POWER_DIVIDER() &&
    getPowerCurrent(alice, PROPOSITION_POWER()) == balanceOf(alice) + getDelegatedPropositionBalance(alice) * DELEGATED_POWER_DIVIDER()
  )
