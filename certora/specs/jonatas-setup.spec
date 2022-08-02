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

/**
    Verify that delegate power update when user send token to another user
*/
rule delegateByTypeCorrectness {
  env e;
  address alice;
  uint8 randomPower;

  uint8 delegateType = randomPower % 2 == 0 ? VOTING_POWER() : PROPOSITION_POWER();

  // delegate not to self or to zero
  require alice != e.msg.sender && alice != 0;

  uint256 aliceDelegatedBalance = getDelegatedVotingBalance(alice);
  // avoid unrealistic delegated balance
  require(aliceDelegatedBalance < MAX_DELEGATED_BALANCE());

  // verify that the sender doesn't already delegate to alice
  address delegateBefore = getVotingDelegate(e.msg.sender);
  require delegateBefore != alice;

  uint256 aliceVotingPowerBefore = getPowerCurrent(alice, VOTING_POWER());
  uint256 alicePropositionPowerBefore = getPowerCurrent(alice, PROPOSITION_POWER());
  uint256 delegatorBalance = balanceOf(e.msg.sender);

  delegateByType(e, alice, delegateType);

  // test the delegate's new voting power
  uint256 aliceVotingPowerAfter = getPowerCurrent(alice, VOTING_POWER());
  uint256 alicePropositionPowerAfter = getPowerCurrent(alice, PROPOSITION_POWER());

  if (delegateType == VOTING_POWER()){
    // test the delegate indeed has changed to alice
    address delegateAfter = getVotingDelegate(e.msg.sender);
    assert delegateAfter == alice, "Did not delegate to alice";

    assert aliceVotingPowerAfter == aliceVotingPowerBefore + normalize(delegatorBalance) => alicePropositionPowerAfter == alicePropositionPowerBefore, "Invalid Power";
  } else {
    // test the delegate indeed has changed to alice
    address delegateAfter = getPropositionDelegate(e.msg.sender);
    assert delegateAfter == alice, "Did not delegate to alice";

    assert alicePropositionPowerAfter == alicePropositionPowerBefore + normalize(delegatorBalance) => aliceVotingPowerAfter == aliceVotingPowerBefore, "Invalid Power";
  }
}

rule delegateToZeroOrItselfAddresses {
  env e;
  address alice;

  // delegate to self or to zero
  require alice == e.msg.sender || alice == 0;

  uint256 aliceDelegatedBalance = getDelegatedVotingBalance(alice);
  // avoid unrealistic delegated balance
  require(aliceDelegatedBalance < MAX_DELEGATED_BALANCE());

  uint256 aliceVotingPowerBefore = getPowerCurrent(alice, VOTING_POWER());
  uint256 alicePropositionPowerBefore = getPowerCurrent(alice, PROPOSITION_POWER());

  uint256 delegatorBalance = balanceOf(e.msg.sender);

  // don't have delegate it power yet
  require getDelegateeByType(e, alice, PROPOSITION_POWER()) == 0;

  delegate(e, alice);

  // test the delegate's new voting power
  uint256 aliceVotingPowerAfter = getPowerCurrent(alice, VOTING_POWER());
  uint256 alicePropositionPowerAfter = getPowerCurrent(alice, PROPOSITION_POWER());

  assert aliceVotingPowerBefore == aliceVotingPowerAfter => alicePropositionPowerBefore == alicePropositionPowerAfter, "Power Changed";
}

rule delegateChangeToAnotherAddress {
  env e;
  address alice;
  address bob;
  uint8 randomPower;

  uint8 delegateType = randomPower % 2 == 0 ? VOTING_POWER() : PROPOSITION_POWER();

  // delegate not to self or to zero
  require alice != e.msg.sender && alice != 0;
  require bob != e.msg.sender && bob != 0 && bob != alice;

  uint256 aliceDelegatedBalance = getDelegatedVotingBalance(alice);
  // avoid unrealistic delegated balance
  require(aliceDelegatedBalance < MAX_DELEGATED_BALANCE());

  // verify that the sender doesn't already delegate to alice
  address delegateBefore = getVotingDelegate(e.msg.sender);
  require delegateBefore != alice && delegateBefore != bob;

  uint256 aliceVotingPowerBefore = getPowerCurrent(alice, VOTING_POWER());
  uint256 alicePropositionPowerBefore = getPowerCurrent(alice, PROPOSITION_POWER());
  uint256 bobVotingPowerBefore = getPowerCurrent(bob, VOTING_POWER());
  uint256 bobPropositionPowerBefore = getPowerCurrent(bob, PROPOSITION_POWER());
  uint256 delegatorBalance = balanceOf(e.msg.sender);

  delegateByType(e, alice, delegateType);
  delegateByType(e, bob, delegateType);

  // test the delegate's new voting power
  uint256 aliceVotingPowerAfter = getPowerCurrent(alice, VOTING_POWER());
  uint256 alicePropositionPowerAfter = getPowerCurrent(alice, PROPOSITION_POWER());
  uint256 bobVotingPowerAfter = getPowerCurrent(bob, VOTING_POWER());
  uint256 bobPropositionPowerAfter = getPowerCurrent(bob, PROPOSITION_POWER());

  if (delegateType == VOTING_POWER()){
    // test the delegate indeed has changed to alice
    address delegateAfter = getVotingDelegate(e.msg.sender);
    assert delegateAfter == bob, "Did not delegate to alice";

    assert aliceVotingPowerAfter == aliceVotingPowerBefore => alicePropositionPowerAfter == alicePropositionPowerBefore, "Invalid Alice Power";
    assert bobVotingPowerAfter == bobVotingPowerBefore + normalize(delegatorBalance) => bobPropositionPowerAfter == bobPropositionPowerBefore, "Invalid Bob Power";
  } else {
    // test the delegate indeed has changed to alice
    address delegateAfter = getPropositionDelegate(e.msg.sender);
    assert delegateAfter == bob, "Did not delegate to alice";

    assert alicePropositionPowerAfter == alicePropositionPowerBefore + normalize(delegatorBalance) => aliceVotingPowerAfter == aliceVotingPowerBefore, "Invalid Alice Power";
    assert bobPropositionPowerAfter == bobPropositionPowerBefore + normalize(delegatorBalance) => bobVotingPowerAfter == bobVotingPowerBefore, "Invalid Bob Power";
  }
}

rule delegateNotUseDelegatedPower {
  env e;
  address alice;
  address bob;
  uint256 deadline;
  uint8 v;
  bytes32 r;
  bytes32 s;

  // delegate not to self or to zero
  require alice != e.msg.sender && alice != 0;
  require bob != e.msg.sender && bob != 0 && bob != alice;

  uint256 aliceDelegatedBalance = getDelegatedVotingBalance(alice);
  uint256 bobDelegatedBalance = getDelegatedVotingBalance(bob);
  // avoid unrealistic delegated balance
  require(
    aliceDelegatedBalance < MAX_DELEGATED_BALANCE() &&
    bobDelegatedBalance < MAX_DELEGATED_BALANCE()
  );

  // verify that the sender doesn't already delegate to alice
  address senderDelegateBefore = getVotingDelegate(e.msg.sender);
  address aliceDelegateBefore = getVotingDelegate(alice);
  require senderDelegateBefore == 0 && aliceDelegateBefore  == 0;

  uint256 senderVotingPowerBefore = getPowerCurrent(e.msg.sender, VOTING_POWER());
  uint256 senderPropositionPowerBefore = getPowerCurrent(e.msg.sender, PROPOSITION_POWER());
  require senderVotingPowerBefore > 0 && senderPropositionPowerBefore > 0;

  uint256 aliceVotingPowerBefore = getPowerCurrent(alice, VOTING_POWER());
  uint256 alicePropositionPowerBefore = getPowerCurrent(alice, PROPOSITION_POWER());
  require aliceVotingPowerBefore > 0 && alicePropositionPowerBefore > 0;

  uint256 bobVotingPowerBefore = getPowerCurrent(bob, VOTING_POWER());
  uint256 bobPropositionPowerBefore = getPowerCurrent(bob, PROPOSITION_POWER());

  uint256 delegatorBalance = balanceOf(e.msg.sender);
  uint256 aliceBalance = balanceOf(alice);
  require delegatorBalance > 0 && aliceBalance > 0;

  //msg.sender delegate power to alice
  delegate(e, alice);
  //alice delegate voting power to bob
  metaDelegateByType(e,alice,bob,VOTING_POWER(),deadline,v,r,s);

  uint256 aliceVotingPowerAfter = getPowerCurrent(alice, VOTING_POWER());
  uint256 alicePropositionPowerAfter = getPowerCurrent(alice, PROPOSITION_POWER());

  uint256 bobVotingPowerAfter = getPowerCurrent(bob, VOTING_POWER());
  uint256 bobPropositionPowerAfter = getPowerCurrent(bob, PROPOSITION_POWER());

  // test the delegate indeed has changed to alice
  address delegateAfterSender = getVotingDelegate(e.msg.sender);
  assert delegateAfterSender == alice, "Sender did not delegate to alice";

  address delegateAfterAlice = getVotingDelegate(alice);
  assert delegateAfterAlice == bob, "Alice did not delegate to bob";

  // test the delegate's new voting power
  assert aliceVotingPowerAfter == aliceVotingPowerBefore => alicePropositionPowerAfter == alicePropositionPowerBefore, "Invalid Alice Power";

  assert bobVotingPowerAfter == bobVotingPowerBefore + normalize(aliceBalance) => bobPropositionPowerAfter == bobPropositionPowerBefore, "Invalid Bob Power";

}



