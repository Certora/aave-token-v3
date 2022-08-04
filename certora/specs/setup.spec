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
    getDelegationState(address user) returns (uint8) envfree
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

definition ZERO_ADDRESS() returns address = 0;

/**

    Function that normalizes (removes 10 least significant digits) a given param. 
    It mirrors the way delegated balances are stored in the token contract. Since the delegated
    balance is stored as a uint72 variable, delegated amounts (uint256()) are normalized.

*/

function normalize(uint256 amount) returns uint256 {
    return to_uint256(amount / DELEGATED_POWER_DIVIDER() * DELEGATED_POWER_DIVIDER());
}

invariant noDelegationToZeroAddress()
    getDelegatedVotingBalance(ZERO_ADDRESS()) == balanceOf(ZERO_ADDRESS()) 
    && getDelegatedPropositionBalance(ZERO_ADDRESS()) == balanceOf(ZERO_ADDRESS())

invariant zeroAddressDoesNotHoldAnyBalance() 
    balanceOf(ZERO_ADDRESS()) == 0 && 
    getDelegatedVotingBalance(ZERO_ADDRESS()) == 0 && 
    getDelegatedPropositionBalance(ZERO_ADDRESS()) == 0

rule delegatingToAnotherUserRemovesPowerFromOldDelegatee(env e, address alice, address bob) {

    require e.msg.sender != ZERO_ADDRESS(); 
    require e.msg.sender != alice && e.msg.sender != bob;
    require alice != ZERO_ADDRESS() && bob != ZERO_ADDRESS();

    require getVotingDelegate(e.msg.sender) != alice;

    uint72 _votingBalance = getDelegatedVotingBalance(alice);

    delegateByType(e, alice, VOTING_POWER());

    assert getVotingDelegate(e.msg.sender) == alice;

    delegateByType(e, bob, VOTING_POWER());

    assert getVotingDelegate(e.msg.sender) == bob;
    uint72 votingBalance_ = getDelegatedVotingBalance(alice);
    assert alice != bob => votingBalance_ == _votingBalance;
}

rule integrityOfDelegate(env e, address bob) {

    require bob != e.msg.sender;
    require bob != 0;

    address _votingDelegate = getVotingDelegate(e.msg.sender);
    address _propositionDelegate = getPropositionDelegate(e.msg.sender);
    uint72 _delegatedVotingBalance = getDelegatedVotingBalance(bob);
    uint72 _delegatedPropositionBalance = getDelegatedPropositionBalance(bob);
    uint256 _votingPower = getPowerCurrent(bob, VOTING_POWER());
    uint256 _propositionPower = getPowerCurrent(bob, PROPOSITION_POWER());
    uint256 _balance = getBalance(e.msg.sender);

    require bob != _votingDelegate && bob != _propositionDelegate;

    delegate(e, bob);

    address votingDelegate_ = getVotingDelegate(e.msg.sender);
    address propositionDelegate_ = getPropositionDelegate(e.msg.sender);
    uint72 delegatedVotingBalance_ = getDelegatedVotingBalance(bob);
    uint72 delegatedPropositionBalance_ = getDelegatedPropositionBalance(bob);
    uint256 votingPower_ = getPowerCurrent(bob, VOTING_POWER());
    uint256 propositionPower_ = getPowerCurrent(bob, PROPOSITION_POWER());
    uint256 balance_ = getBalance(e.msg.sender);

    assert _delegatedVotingBalance + _balance/DELEGATED_POWER_DIVIDER() == delegatedVotingBalance_;  
    assert _delegatedPropositionBalance + _balance/DELEGATED_POWER_DIVIDER() == delegatedPropositionBalance_;
    assert votingPower_ == _votingPower + normalize(_balance);
    assert propositionPower_ == _propositionPower + normalize(_balance);
    assert _votingDelegate != votingDelegate_;
    assert _propositionDelegate != propositionDelegate_;
    assert votingDelegate_ == propositionDelegate_;
    assert _balance == balance_;
}

rule integrityOfDelegateByType(env e, address alice, address bob) {

    require e.msg.sender != alice && alice != ZERO_ADDRESS();
    require e.msg.sender != bob && bob != ZERO_ADDRESS();

    address _votingDelegate = getVotingDelegate(e.msg.sender);
    address _propositionDelegate = getPropositionDelegate(e.msg.sender);
    uint72 _votingBalance = getDelegatedVotingBalance(alice);
    uint256 _votingPower = getPowerCurrent(alice, VOTING_POWER());
    uint72 _propositionBalance = getDelegatedPropositionBalance(bob);
    uint256 _propositionPower = getPowerCurrent(bob, PROPOSITION_POWER());
    uint256 _balance = getBalance(e.msg.sender);

    require alice != _votingDelegate && bob != _propositionDelegate;

    delegateByType(e, alice, VOTING_POWER());
    delegateByType(e, bob, PROPOSITION_POWER());

    address votingDelegate_ = getVotingDelegate(e.msg.sender);
    address propositionDelegate_ = getPropositionDelegate(e.msg.sender);
    uint72 votingBalance_ = getDelegatedVotingBalance(alice);
    uint256 votingPower_ = getPowerCurrent(alice, VOTING_POWER());
    uint72 propositionBalance_ = getDelegatedPropositionBalance(bob);
    uint256 propositionPower_ = getPowerCurrent(bob, PROPOSITION_POWER());
    uint256 balance_ = getBalance(e.msg.sender);

    assert votingPower_ == _votingPower + normalize(_balance);
    assert propositionPower_ == _propositionPower + normalize(_balance);
    assert _propositionDelegate != propositionDelegate_;
    assert _votingBalance + _balance/DELEGATED_POWER_DIVIDER() == votingBalance_;
    assert _propositionBalance + _balance/DELEGATED_POWER_DIVIDER() == propositionBalance_;
    assert _votingDelegate != votingDelegate_;
    assert _balance == balance_;

}

rule delegateAnddelegateByTypeAreEquivalent(env e, address bob) {

    require bob != e.msg.sender && bob != ZERO_ADDRESS();

    storage initialStorage = lastStorage;

    delegateByType(e, bob, VOTING_POWER());
    delegateByType(e, bob, PROPOSITION_POWER());

    address votingDelegate0_ = getVotingDelegate(e.msg.sender);
    address propositionDelegate0_ = getPropositionDelegate(e.msg.sender);
    uint72 votingBalance0_ = getDelegatedVotingBalance(bob);
    uint72 propositionBalance0_ = getDelegatedPropositionBalance(bob);
    uint256 votingPower0_ = getPowerCurrent(bob, VOTING_POWER());
    uint256 propositionPower0_ = getPowerCurrent(bob, PROPOSITION_POWER());

    delegate(e, bob) at initialStorage;

    address votingDelegate1_ = getVotingDelegate(e.msg.sender);
    address propositionDelegate1_ = getPropositionDelegate(e.msg.sender);
    uint72 votingBalance1_ = getDelegatedVotingBalance(bob);
    uint72 propositionBalance1_ = getDelegatedPropositionBalance(bob);
    uint256 votingPower1_ = getPowerCurrent(bob, VOTING_POWER());
    uint256 propositionPower1_ = getPowerCurrent(bob, PROPOSITION_POWER());

    assert votingPower0_ == votingPower1_;
    assert propositionPower0_ == propositionPower1_;
    assert votingDelegate0_ == votingDelegate1_;
    assert propositionDelegate0_ == propositionDelegate1_;
    assert votingBalance0_ == votingBalance1_;
    assert propositionBalance0_ == propositionBalance1_;
}

// @MCERFSR: failing for function _governancePowerTransferByType but it should be internal and not public
rule stateTrasitionOfVotingPower(env e, address bob, method f, calldataarg args, address from, address to, uint256 amount) {
    
    uint256 _votingPower = getPowerCurrent(bob, 0);

    if(f.selector == transferFrom(address,address,uint256).selector) {
        transferFrom(e, from, to, amount);
    } else if(f.selector == transfer(address,uint256).selector) {
        transfer(e, to, amount);
    } else {
         f(e, args);
    }

    uint256 votingPower_ = getPowerCurrent(bob, 0);

    assert votingPower_ > 0 && _votingPower == 0 => balanceOf(bob) > 0 || getVotingDelegate(e.msg.sender) == bob ||
    getVotingDelegate(to) == bob || f.selector == metaDelegate(address,address,uint256,uint8,bytes32,bytes32).selector ||
        f.selector == metaDelegateByType(address,address,uint8,uint256,uint8,bytes32,bytes32).selector;
}

rule addressZeroDoesNotGetAnyPower(env e) {
    address _votingDelegate = getVotingDelegate(e.msg.sender);
    address _propositionDelegate = getPropositionDelegate(e.msg.sender);
    uint256 _balance = balanceOf(e.msg.sender);
    uint72 _votingBalance = getDelegatedVotingBalance(ZERO_ADDRESS());
    uint72 _propositionBalance = getDelegatedPropositionBalance(ZERO_ADDRESS());

    require _votingDelegate != ZERO_ADDRESS() && _propositionDelegate != ZERO_ADDRESS();
    require _votingBalance == 0 && _propositionBalance == 0;

    delegate(e, ZERO_ADDRESS());

    address votingDelegate_ = getVotingDelegate(e.msg.sender);
    address propositionDelegate_ = getPropositionDelegate(e.msg.sender);
    uint256 balance_ = balanceOf(e.msg.sender);
    uint72 votingBalance_ = getDelegatedVotingBalance(ZERO_ADDRESS());
    uint72 propositionBalance_ = getDelegatedPropositionBalance(ZERO_ADDRESS());

    assert votingBalance_ == 0;
    assert propositionBalance_ == 0;
    assert _balance == balance_;

}

rule powerEqualsToBalanceIfThereIsNoDelegation(env e, address bob) {

    uint256 _balance = balanceOf(bob);

    uint256 votingPower = getPowerCurrent(bob, VOTING_POWER());
    uint256 propositionPower = getPowerCurrent(bob, PROPOSITION_POWER());
    uint256 votingBalance = getDelegatedVotingBalance(bob);
    uint256 propositionBalance = getDelegatedPropositionBalance(bob);
    address votingDelegate = getVotingDelegate(bob);
    address propositionDelegate = getPropositionDelegate(bob);
    
    require votingBalance == 0 && propositionBalance == 0;
    require getDelegationState(bob) == 0;

    assert votingPower == _balance;
    assert propositionPower == _balance;    
} 

rule delegateToOwnAddress(env e, address bob) {
    require bob == e.msg.sender;

    uint256 _balance = balanceOf(bob);
    uint256 _votingPower = getPowerCurrent(bob, VOTING_POWER());
    uint256 _propositionPower = getPowerCurrent(bob, PROPOSITION_POWER());
    uint256 _votingBalance = getDelegatedVotingBalance(bob);
    uint256 _propositionBalance = getDelegatedPropositionBalance(bob);
    address _votingDelegate = getVotingDelegate(bob);
    address _propositionDelegate = getPropositionDelegate(bob);

    delegate(e, bob);

    uint256 balance_ = balanceOf(bob);
    uint256 votingPower_ = getPowerCurrent(bob, VOTING_POWER());
    uint256 propositionPower_ = getPowerCurrent(bob, PROPOSITION_POWER());
    uint256 votingBalance_ = getDelegatedVotingBalance(bob);
    uint256 propositionBalance_ = getDelegatedPropositionBalance(bob);
    address votingDelegate_ = getVotingDelegate(bob);
    address propositionDelegate_ = getPropositionDelegate(bob);

    assert _balance == balance_;
    assert _balance == balance_;
    assert _votingBalance == votingBalance_;
    assert _propositionBalance == propositionBalance_;
}

rule delegateToOtherIncreasesPowerOfOther(env e, address alice, address bob) {
    
    require e.msg.sender != alice && alice != ZERO_ADDRESS();
    require e.msg.sender != bob && bob != ZERO_ADDRESS();
    require alice != bob;
    
    address _votingDelegate = getVotingDelegate(e.msg.sender);
    address _propositionDelegate = getPropositionDelegate(e.msg.sender);
    require _votingDelegate != alice && _votingDelegate != bob;
    require _propositionDelegate != alice && _propositionDelegate != bob;
    uint104 _balance = getBalance(e.msg.sender);
    uint72 _votingBalance = getDelegatedVotingBalance(bob);
    uint72 _propositionBalance = getDelegatedPropositionBalance(bob);
    uint256 _votingPower1 = getPowerCurrent(alice, VOTING_POWER());
    uint256 _propositionPower1 = getPowerCurrent(alice, PROPOSITION_POWER());

    delegate(e, alice);

    assert getVotingDelegate(e.msg.sender) == alice;
    assert getPropositionDelegate(e.msg.sender) == alice;
    assert getDelegatedVotingBalance(bob) == _votingBalance;
    assert getDelegatedPropositionBalance(bob) == _propositionBalance;

    delegate(e, bob);

    uint72 votingBalance1 = getDelegatedVotingBalance(alice);
    uint72 propositionBalance1 = getDelegatedPropositionBalance(alice);
    uint256 votingPower1_ = getPowerCurrent(alice, VOTING_POWER());
    uint256 propositionPower1_ = getPowerCurrent(alice, PROPOSITION_POWER());

    uint104 balance_ = getBalance(e.msg.sender);
    uint72 votingBalance_ = getDelegatedVotingBalance(bob);
    uint72 propositionBalance_ = getDelegatedPropositionBalance(bob);
    address votingDelegate_ = getVotingDelegate(e.msg.sender);
    address propositionDelegate_ = getPropositionDelegate(e.msg.sender);

    assert votingDelegate_ == bob;
    assert propositionDelegate_ == bob;
    assert votingBalance_ == _votingBalance + _balance/DELEGATED_POWER_DIVIDER();
    assert propositionBalance_ == _propositionBalance + _balance/DELEGATED_POWER_DIVIDER();
    assert _balance == balance_;
    assert _votingPower1 == votingPower1_;
    assert _propositionPower1 == propositionPower1_;
}

rule accountPowerAndBalanceRelation(env e, address bob) {
    
    uint256 votingPower = getPowerCurrent(bob, VOTING_POWER());
    uint256 propositionPower = getPowerCurrent(bob, PROPOSITION_POWER());
    uint8 delegationState = getDelegationState(bob);
    uint72 votingBalance = getDelegatedVotingBalance(bob);
    uint72 propositionBalance = getDelegatedPropositionBalance(bob);
    uint104 balance = getBalance(bob);

    assert delegationState == 0 => votingPower == votingBalance * DELEGATED_POWER_DIVIDER() + balance;
    assert delegationState == 1 => votingPower == votingBalance * DELEGATED_POWER_DIVIDER();
    assert delegationState == 2 => votingPower == votingBalance * DELEGATED_POWER_DIVIDER() + balance;
    assert delegationState == 3 => votingPower == votingBalance * DELEGATED_POWER_DIVIDER();
    assert delegationState == 0 => propositionPower == propositionBalance * DELEGATED_POWER_DIVIDER() + balance;
    assert delegationState == 1 => propositionPower == propositionBalance * DELEGATED_POWER_DIVIDER() + balance;
    assert delegationState == 2 => propositionPower == propositionBalance * DELEGATED_POWER_DIVIDER();
    assert delegationState == 3 => propositionPower == propositionBalance * DELEGATED_POWER_DIVIDER();

}

rule powerOnDelegationIncreasesByBalanceOfSender(env e, address bob) {

    require e.msg.sender != 0 && e.msg.sender != bob && bob != 0;
    
    uint256 _votingPower = getPowerCurrent(bob, VOTING_POWER());
    uint256 _propositionPower = getPowerCurrent(bob, PROPOSITION_POWER());
    uint8 _delegationState = getDelegationState(bob);
    uint72 _votingBalance = getDelegatedVotingBalance(bob);
    uint72 _propositionBalance = getDelegatedPropositionBalance(bob);
    uint104 _balance = getBalance(e.msg.sender);
    address _votingDelegate = getVotingDelegate(bob);
    address _propositionDelegate = getPropositionDelegate(bob);

    require getVotingDelegate(e.msg.sender) != bob && getPropositionDelegate(e.msg.sender) != bob;

    delegate(e, bob);

    uint256 votingPower_ = getPowerCurrent(bob, VOTING_POWER());
    uint256 propositionPower_ = getPowerCurrent(bob, PROPOSITION_POWER());
    uint8 delegationState_ = getDelegationState(bob);
    uint72 votingBalance_ = getDelegatedVotingBalance(bob);
    uint72 propositionBalance_ = getDelegatedPropositionBalance(bob);
    uint104 balance_ = getBalance(e.msg.sender);
    address votingDelegate_ = getVotingDelegate(bob);
    address propositionDelegate_ = getPropositionDelegate(bob);

    assert _balance == balance_;
    assert propositionPower_ == _propositionPower + normalize(_balance);
    assert votingPower_ == _votingPower + normalize(_balance);
    assert votingBalance_ == _votingBalance + _balance/DELEGATED_POWER_DIVIDER();
    assert propositionBalance_ == _propositionBalance + _balance/DELEGATED_POWER_DIVIDER();
    assert _delegationState == delegationState_;
    assert _votingDelegate == votingDelegate_;
    assert _propositionDelegate == propositionDelegate_;
    assert getVotingDelegate(e.msg.sender) == bob;
    assert getPropositionDelegate(e.msg.sender) == bob;
}

rule delegateOnlyChangeBySpecialMethods(env e, address bob, method f, calldataarg args) {

    address _votingDelegate = getVotingDelegate(bob);
    address _propositionDelegate = getPropositionDelegate(bob);

    f(e, args);

    address votingDelegate_ = getVotingDelegate(bob);
    address propositionDelegate_ = getPropositionDelegate(bob);

    require (_votingDelegate != votingDelegate_) || (_propositionDelegate != propositionDelegate_);

    assert f.selector == delegate(address).selector 
    || f.selector == delegateByType(address,uint8).selector 
    || f.selector == metaDelegate(address,address,uint256,uint8,bytes32,bytes32).selector 
    || f.selector == metaDelegateByType(address,address,uint8,uint256,uint8,bytes32,bytes32).selector;
 }

 rule otherUserCanChangeDelegateWithMetaFunction(env e, address bob, method f, calldataarg args) {

    address _votingDelegate = getVotingDelegate(bob);
    address _propositionDelegate = getPropositionDelegate(bob);

    f(e, args);

    address votingDelegate_ = getVotingDelegate(bob);
    address propositionDelegate_ = getPropositionDelegate(bob);

    require _votingDelegate != votingDelegate_ || _propositionDelegate != propositionDelegate_;
    require e.msg.sender != bob;

     assert f.selector == metaDelegate(address,address,uint256,uint8,bytes32,bytes32).selector 
     || f.selector == metaDelegateByType(address,address,uint8,uint256,uint8,bytes32,bytes32).selector;

}

rule delegationDoesNotChangeOther(env e, address alice, address bob) {

    storage initialState = lastStorage;
    address _votingDelegate = getVotingDelegate(alice);
    uint104 _balance0 = getBalance(alice);
    delegateByType(e, bob, PROPOSITION_POWER());
    address votingDelegate_ = getVotingDelegate(alice);
    uint104 balance0_ = getBalance(alice);

    address _balance1 = getBalance(alice) at initialState;
    address _propositionDelegate = getPropositionDelegate(alice);
    delegateByType(e, bob, VOTING_POWER());
    address propositionDelegate_ = getPropositionDelegate(alice);
    address balance1_ = getBalance(alice);

    assert _votingDelegate == votingDelegate_;
    assert _propositionDelegate == propositionDelegate_;
    assert _balance0 == balance0_;
    assert _balance1 == balance1_;
}

rule oneMetaDelegationDoesNotChangeOther(env e, address alice, address bob, uint256 deadline, uint8 v, bytes32 r, bytes32 s) {
    
    storage initialState = lastStorage;
    address _votingDelegate = getVotingDelegate(alice);
    metaDelegateByType(e, alice, bob, PROPOSITION_POWER(), deadline, v, r, s);
    address votingDelegate_ = getVotingDelegate(alice);

    address _propositionDelegate = getPropositionDelegate(alice) at initialState;
    metaDelegateByType(e, alice, bob, VOTING_POWER(), deadline, v, r, s);
    address propositionDelegate_ = getPropositionDelegate(alice);

    assert _votingDelegate == votingDelegate_;
    assert _propositionDelegate == propositionDelegate_;
}

rule delegateIsNotTransitive(env e1, env e2, address alice, address bob, address sam) {
    
    storage initialState = lastStorage;

    require e1.msg.sender == alice;
    require e2.msg.sender == bob;
    require alice != sam && alice != bob && bob != sam;
    require alice != ZERO_ADDRESS() && bob != ZERO_ADDRESS() && sam != ZERO_ADDRESS();

    delegate(e1, bob);
    delegate(e2, sam);

    address votingDelegateOf1 = getVotingDelegate(alice);
    address propositionDelegate1 = getPropositionDelegate(alice);

    assert votingDelegateOf1 != sam;
    assert propositionDelegate1 != sam;

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