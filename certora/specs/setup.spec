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
    getDelegationState(address a) returns (uint8) envfree
    transferFrom(address from, address to, uint256 amount) returns (bool)
    delegate(address delegatee)
    permit(address, address, uint256, uint256, uint8, bytes32, bytes32)
    metaDelegate(address, address, uint256, uint8, bytes32, bytes32)
    metaDelegateByType(address, address, uint8, uint256, uint8, bytes32, bytes32)
    getPowerCurrent(address user, uint8 delegationType) returns (uint256) envfree
    getBalance(address user) returns (uint104) envfree
    getDelegatedPropositionBalance(address user) returns (uint72) envfree
    getDelegatedVotingBalance(address user) returns (uint72) envfree
    getDelegatingProposition(address user) returns (bool) envfree
    getDelegatingVoting(address user) returns (bool) envfree
    getVotingDelegate(address user) returns (address) envfree
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

/*
    NOTE:

    Legend: 
    Variable name that ends with 0 means before the method call ex: user0, balance0
    Variable name that ends with 1 means after the method call ex: user1, balance1
*/

invariant zeroAddressCanNotBeDelegatedToOrTransferredTo()
    getDelegatedVotingBalance(0) == balanceOf(0) && getDelegatedPropositionBalance(0) == balanceOf(0) && balanceOf(0) == 0

rule balanceChangeIntegrity(env e)
{
    address user1; 
    address user2;
    method f;

	require user1!=user2;
	uint256 balanceA0 = balanceOf(user1);
	uint256 balanceB0 = balanceOf(user2);
	 
	calldataarg arg;
	f(e, arg); 
	uint256 balanceA1 = balanceOf(user1);
	uint256 balanceB1 = balanceOf(user2);
	
	assert (balanceA0 == balanceA1 || balanceB0 == balanceB1 || 
        (balanceA0 != balanceA1 && balanceB0 != balanceB1 && balanceA0+balanceB0 == balanceA1+balanceB1)
    );
}

rule integrityBalanceOfAndTotalSupply(address user, method f ) filtered {
	f -> f.selector != transferFrom(address,address,uint256).selector
        && f.selector != transfer(address,uint256).selector
	}
{
	env e;
    calldataarg arg;
	uint256 balance0 = balanceOf(user);
	uint256 totalSupply0 = totalSupply();

	f(e, arg);

	uint256 balance1 = balanceOf(user);
	uint256 totalSupply1 = totalSupply();
	assert  (balance1 != balance0  => (balance1 - balance0  == totalSupply1 - totalSupply0));
}

rule integrityOfDelegateByType(env e) {

    address user0;

    require e.msg.sender != user0 && user0 != 0;

    address votingDelegate0 = getVotingDelegate(e.msg.sender);
    address propositionDelegate0 = getPropositionDelegate(e.msg.sender);
    uint256 votingPower0 = getPowerCurrent(user0, VOTING_POWER());
    uint256 propositionPower0 = getPowerCurrent(user0, PROPOSITION_POWER());
    uint72 votingBalance0 = getDelegatedVotingBalance(user0);
    uint72 propositionBalance0 = getDelegatedPropositionBalance(user0);
    uint256 balance0 = balanceOf(e.msg.sender);

    require user0 != votingDelegate0 && user0 != propositionDelegate0;

    delegateByType(e, user0, VOTING_POWER());
    delegateByType(e, user0, PROPOSITION_POWER());

    uint256 votingPower1 = getPowerCurrent(user0, VOTING_POWER());
    uint256 propositionPower1 = getPowerCurrent(user0, PROPOSITION_POWER());
    address votingDelegate1 = getVotingDelegate(e.msg.sender);
    address propositionDelegate1 = getPropositionDelegate(e.msg.sender);
    uint72 votingBalance1 = getDelegatedVotingBalance(user0);
    uint72 propositionBalance1 = getDelegatedPropositionBalance(user0);


    assert votingDelegate0 != votingDelegate1;
    assert propositionDelegate0 != propositionDelegate1;
    assert votingBalance0 + balance0/DELEGATED_POWER_DIVIDER() == votingBalance1;
    assert propositionBalance0 + balance0/DELEGATED_POWER_DIVIDER() == propositionBalance1;
    assert votingPower1 == votingPower0 + normalize(balance0);
    assert propositionPower1 == propositionPower0 + normalize(balance0);
}

rule delegationNoInterference(env e) {

    address user0;
    address user1;

    require user0 != 0 && user1 != 0 && user0 != user1;
    require getVotingDelegate(e.msg.sender) != user0 && getPropositionDelegate(e.msg.sender) != user0;
    require getVotingDelegate(user1) != user0 && getPropositionDelegate(user1) != user0;
    require e.msg.sender != user0 && e.msg.sender != user1;

    address votingDelegate0 = getVotingDelegate(user0);
    address propositionDelegate0 = getPropositionDelegate(user0);
    uint104 balance0 = getBalance(user0);
    uint256 votingBalance0 = getDelegatedVotingBalance(user0);
    uint256 propositionBalance0 = getDelegatedPropositionBalance(user0);
    uint256 votingPower0 = getPowerCurrent(user0, VOTING_POWER());
    delegate(e, user1);
    address votingDelegate1 = getVotingDelegate(user0);
    uint104 balance1 = getBalance(user0);
    address propositionDelegate1 = getPropositionDelegate(user0);
    uint256 votingBalance1 = getDelegatedVotingBalance(user0);
    uint256 propositionBalance1 = getDelegatedPropositionBalance(user0);
    uint256 votingPower1 = getPowerCurrent(user0, VOTING_POWER());


    assert votingDelegate0 == votingDelegate1;
    assert propositionDelegate0 == propositionDelegate1;
    assert balance0 == balance1;
    assert votingBalance0 == votingBalance1;
    assert propositionBalance0 == propositionBalance1;
    assert votingPower0 == votingPower1;
}

rule revokingShouldRemovePowerFromPreviousAndGiveToNew(env e) {

    address user0;
    address user1;

    require e.msg.sender != 0; 
    require e.msg.sender != user0 && e.msg.sender != user1;
    require user0 != 0 && user1 != 0;

    address votingDelegate0 = getVotingDelegate(e.msg.sender);

    require votingDelegate0 != user0;

    uint72 votingBalance0 = getDelegatedVotingBalance(user0);

    delegateByType(e, user0, VOTING_POWER());

    address votingDelegate1 = getVotingDelegate(e.msg.sender);

    assert votingDelegate1 == user0;

    delegateByType(e, user1, VOTING_POWER());

    address votingDelegate2 = getVotingDelegate(e.msg.sender);

    assert votingDelegate2 == user1;
    uint72 votingBalance2 = getDelegatedVotingBalance(user0);
    assert user0 != user1 => votingBalance2 == votingBalance0;
}

rule integrityOfDelegate(env e) {

    address user;
    address sender = e.msg.sender;

    require user != sender;
    require user != 0;

    address votingDelegate0 = getVotingDelegate(sender);
    address propositionDelegate0 = getPropositionDelegate(sender);
    uint72 delegatedVotingBalance0 = getDelegatedVotingBalance(user);
    uint72 delegatedPropositionBalance0 = getDelegatedPropositionBalance(user);
    uint256 votingPower0 = getPowerCurrent(user, VOTING_POWER());
    uint256 propositionPower0 = getPowerCurrent(user, PROPOSITION_POWER());
    uint256 balance0 = getBalance(sender);

    require user != votingDelegate0 && user != propositionDelegate0;

    delegate(e, user);

    address votingDelegate1 = getVotingDelegate(sender);
    address propositionDelegate1 = getPropositionDelegate(sender);
    uint72 delegatedVotingBalance1 = getDelegatedVotingBalance(user);
    uint72 delegatedPropositionBalance1 = getDelegatedPropositionBalance(user);
    uint256 votingPower1 = getPowerCurrent(user, VOTING_POWER());
    uint256 propositionPower1 = getPowerCurrent(user, PROPOSITION_POWER());

    assert delegatedVotingBalance0 + balance0/DELEGATED_POWER_DIVIDER() == delegatedVotingBalance1;  
    assert delegatedPropositionBalance0 + balance0/DELEGATED_POWER_DIVIDER() == delegatedPropositionBalance1;
    assert votingDelegate0 != votingDelegate1;
    assert propositionDelegate0 != propositionDelegate1;
    assert votingPower1 == votingPower0 + normalize(balance0);
    assert propositionPower1 == propositionPower0 + normalize(balance0);
}

rule equivalentDelegateAnddelegateByType(env e) {

    address user;
    address sender = e.msg.sender;

    require user != sender && user != 0;

    storage state = lastStorage;

    delegateByType(e, user, VOTING_POWER());
    delegateByType(e, user, PROPOSITION_POWER());

    address votingDelegate0 = getVotingDelegate(sender);
    address propositionDelegate0 = getPropositionDelegate(sender);
    uint72 votingBalance0 = getDelegatedVotingBalance(user);
    uint72 propositionBalance0 = getDelegatedPropositionBalance(user);
    uint256 votingPower0 = getPowerCurrent(user, VOTING_POWER());
    uint256 propositionPower0 = getPowerCurrent(user, PROPOSITION_POWER());

    delegate(e, user) at state;

    address votingDelegate1 = getVotingDelegate(sender);
    address propositionDelegate1 = getPropositionDelegate(sender);
    uint72 votingBalance1 = getDelegatedVotingBalance(user);
    uint72 propositionBalance1 = getDelegatedPropositionBalance(user);
    uint256 votingPower1 = getPowerCurrent(user, VOTING_POWER());
    uint256 propositionPower1 = getPowerCurrent(user, PROPOSITION_POWER());

    assert votingBalance0 == votingBalance1;
    assert propositionBalance0 == propositionBalance1;
    assert votingDelegate0 == votingDelegate1;
    assert propositionDelegate0 == propositionDelegate1;
    assert votingPower0 == votingPower1;
    assert propositionPower0 == propositionPower1;
}


rule powerEqualsToBalanceCondition(env e) {

    address user;

    uint256 balance0 = balanceOf(user);
    uint8 delegationState0 = getDelegationState(user);
    uint256 votingPower0 = getPowerCurrent(user, VOTING_POWER());
    uint256 propositionPower0 = getPowerCurrent(user, PROPOSITION_POWER());
    uint256 votingBalance0 = getDelegatedVotingBalance(user);
    uint256 propositionBalance0 = getDelegatedPropositionBalance(user);
    address votingDelegate0 = getVotingDelegate(user);
    address propositionDelegate0 = getPropositionDelegate(user);

    require votingBalance0 == 0 && propositionBalance0 == 0;
    require delegationState0 == 0;

    assert votingPower0 == balance0;
    assert propositionPower0 == balance0;    
} 

rule delegateToOwnAddressDoesNotChangeAnything(env e) {
    address user;

    require user == e.msg.sender;

    uint256 balance0 = balanceOf(user);
    uint256 votingBalance0 = getDelegatedVotingBalance(user);
    uint256 propositionBalance0 = getDelegatedPropositionBalance(user);

    delegate(e, user);

    uint256 balance1 = balanceOf(user);
    uint256 votingBalance1 = getDelegatedVotingBalance(user);
    uint256 propositionBalance1 = getDelegatedPropositionBalance(user);

    assert balance0 == balance1;
    assert votingBalance0 == votingBalance1;
    assert propositionBalance0 == propositionBalance1;
}

rule delegateChangesBySpecialMethods(env e, address bob, method f, calldataarg args) {

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

rule powerOnDelegationIncreases(env e) {

    address user;

    require e.msg.sender != 0 && e.msg.sender != user && user != 0;
    
    uint256 votingPower0 = getPowerCurrent(user, VOTING_POWER());
    uint256 propositionPower0 = getPowerCurrent(user, PROPOSITION_POWER());
    uint72 votingBalance0 = getDelegatedVotingBalance(user);
    uint72 propositionBalance0 = getDelegatedPropositionBalance(user);
    uint104 balance0 = getBalance(e.msg.sender);

    require getVotingDelegate(e.msg.sender) != user && getPropositionDelegate(e.msg.sender) != user;

    delegate(e, user);

    uint256 votingPower1 = getPowerCurrent(user, VOTING_POWER());
    uint256 propositionPower1 = getPowerCurrent(user, PROPOSITION_POWER());
    uint72 votingBalance1 = getDelegatedVotingBalance(user);
    uint72 propositionBalance1 = getDelegatedPropositionBalance(user);

    assert propositionPower1 == propositionPower0 + normalize(balance0);
    assert votingPower1 == votingPower0 + normalize(balance0);
    assert votingBalance1 == votingBalance0 + balance0/DELEGATED_POWER_DIVIDER();
    assert propositionBalance1 == propositionBalance0 + balance0/DELEGATED_POWER_DIVIDER();
}

rule nonceCanOnlyChangeByCertainFunction() {
    
    address user;
    calldataarg args;
    method f;
    env e;

    uint256 nonce0 = getNonce(user);

    f(e, args);

    uint256 nonce1 = getNonce(user);
    assert nonce0 != nonce1 =>  f.selector == metaDelegate(address,address,uint256,uint8,bytes32,bytes32).selector ||
        f.selector == metaDelegateByType(address,address,uint8,uint256,uint8,bytes32,bytes32).selector ||
        f.selector == permit(address,address,uint256,uint256,uint8,bytes32,bytes32).selector;
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