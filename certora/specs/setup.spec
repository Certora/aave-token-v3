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
    getDelegationState(address user) returns (uint8) envfree
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

invariant zeroAddressPower()
    getDelegatedPropositionBalance(0) == balanceOf(0) && getDelegatedVotingBalance(0) == balanceOf(0)

invariant zeroAddressBalance() 
    getBalance(0) == 0


rule notTransitivityOfDelegate(env e1, env e2, address userA, address userB, address userC) {
    
    require userA != userC && userA != userB && userB != userC;
    require userA != 0 && userB != 0 && userC != 0;
    address sender1 = e1.msg.sender;
    address sender2 = e2.msg.sender;

    require sender1 == userA;
    require sender2 == userB;

    delegate(e1, userB);
    delegate(e2, userC);

    address votingDelegate = getVotingDelegate(userA);
    address propositionDelegate = getPropositionDelegate(userA);
    address votingDelegateB = getVotingDelegate(userB);
    address propositionDelegateB = getPropositionDelegate(userB);

    assert votingDelegate != userC;
    assert votingDelegateB == userC;
    assert propositionDelegate != userC;
    assert propositionDelegateB == userC;

}

rule delegateIntegrity(env e, address user) {

    address sender = e.msg.sender;
    require user != sender;
    require user != 0;

    uint256 initialAaveBalance = getBalance(sender);
    uint256 initialVotingPower = getPowerCurrent(user, VOTING_POWER());
    uint256 initialPropositionPower = getPowerCurrent(user, PROPOSITION_POWER());
    uint72 initialDelegatedVotingBalance = getDelegatedVotingBalance(user);
    uint72 initialDelegatedPropositionBalance = getDelegatedPropositionBalance(user);
    address initialVotingDelegate = getVotingDelegate(sender);
    address initialPropositionDelegate = getPropositionDelegate(sender);

    require user != initialVotingDelegate && user != initialPropositionDelegate;

    delegate(e, user);

    uint256 finalAaveBalance = getBalance(sender);
    uint256 finalVotingPower = getPowerCurrent(user, VOTING_POWER());
    uint256 finalPropositionPower = getPowerCurrent(user, PROPOSITION_POWER());
    uint72 finalDelegatedVotingBalance = getDelegatedVotingBalance(user);
    uint72 finalDelegatedPropositionBalance = getDelegatedPropositionBalance(user);
    address finalVotingDelegate = getVotingDelegate(sender);
    address finalPropositionDelegate = getPropositionDelegate(sender);

    assert initialPropositionDelegate != finalPropositionDelegate;
    assert finalDelegatedPropositionBalance == initialDelegatedPropositionBalance + initialAaveBalance/10^10;
    assert finalPropositionPower == initialPropositionPower + normalize(finalAaveBalance);


    assert finalDelegatedVotingBalance == initialDelegatedVotingBalance + initialAaveBalance/10^10;  
    assert finalVotingPower == initialVotingPower + normalize(finalAaveBalance);
    assert initialVotingDelegate != finalVotingDelegate;


    assert initialAaveBalance == finalAaveBalance;
}

rule delegateByTypeIntegrity(env e, address userA) {

    address sender = e.msg.sender;
    require userA != 0;
    require sender != userA;

    address initialPropositionDelegate = getPropositionDelegate(sender);
    address initialVotingDelegate = getVotingDelegate(sender);
    uint72 initialPropositionBalance = getDelegatedPropositionBalance(userA);
    uint256 initialVotingPower = getPowerCurrent(userA, VOTING_POWER());
    uint256 initialPropositionPower = getPowerCurrent(userA, PROPOSITION_POWER());
    uint72 initialVotingBalance = getDelegatedVotingBalance(userA);
    uint256 initialBalance = getBalance(sender);

    require userA != initialVotingDelegate;
    require userA != initialPropositionDelegate;

    delegateByType(e, userA, VOTING_POWER());
    delegateByType(e, userA, PROPOSITION_POWER());

    address finalPropositionDelegate = getPropositionDelegate(sender);
    address finalVotingDelegate = getVotingDelegate(sender);
    uint256 finalVotingPower = getPowerCurrent(userA, VOTING_POWER());
    uint256 finalPropositionPower = getPowerCurrent(userA, PROPOSITION_POWER());
    mathint finalPropositionBalance = getDelegatedPropositionBalance(userA);
    mathint finalVotingBalance = getDelegatedVotingBalance(userA);
    uint256 finalBalance = getBalance(sender);

    assert initialBalance == finalBalance;
    assert initialVotingDelegate != finalVotingDelegate;
    assert initialPropositionDelegate != finalPropositionDelegate;
    assert initialVotingBalance + finalBalance/10^10 == finalVotingBalance;
    assert initialPropositionBalance + finalBalance/10^10 == finalPropositionBalance;
    assert finalPropositionPower == initialPropositionPower + normalize(finalBalance);
    assert finalVotingPower == initialVotingPower + normalize(finalBalance);
}

rule delegationToNewUser(env e, address userA, address userB) {

    require e.msg.sender != 0; 
    require e.msg.sender != userA;
    require e.msg.sender != userB;
    require userA != 0 && userB != 0;

    require userA != userB;

    require getVotingDelegate(e.msg.sender) != userA;
    require getPropositionDelegate(e.msg.sender) != userA;

    uint72 initialVotingBalance = getDelegatedVotingBalance(userA);
    uint72 initialPropositionBalance = getDelegatedPropositionBalance(userA);

    delegateByType(e, userA, VOTING_POWER());
    delegateByType(e, userA, PROPOSITION_POWER());

    assert getVotingDelegate(e.msg.sender) == userA;
    assert getPropositionDelegate(e.msg.sender) == userA;

    delegateByType(e, userB, VOTING_POWER());
    delegateByType(e, userB, PROPOSITION_POWER());

    assert getVotingDelegate(e.msg.sender) == userB;
    assert getPropositionDelegate(e.msg.sender) == userB;
    uint72 finalVotingBalance = getDelegatedVotingBalance(userA);
    uint72 finalPropositionBalance = getDelegatedPropositionBalance(userA);
    assert finalPropositionBalance == initialPropositionBalance;
    assert finalVotingBalance == initialVotingBalance;
}

rule equivalenceOfDelegateAndDelegateByType(env e, address user) {
    
    address sender = e.msg.sender;

    require user != sender;
    require user != 0;
    
    storage oldState = lastStorage;

    delegate(e, user) at oldState;

    address finalPropositionDelegate1 = getPropositionDelegate(sender);
    address finalVotingDelegate1 = getVotingDelegate(sender);
    uint72 finalPropositionBalance1 = getDelegatedPropositionBalance(user);
    uint72 finalVotingBalance1 = getDelegatedVotingBalance(user);

    delegateByType(e, user, VOTING_POWER()) at oldState;
    delegateByType(e, user, PROPOSITION_POWER());

    address finalPropositionDelegate2 = getPropositionDelegate(sender);
    address finalVotingDelegate2 = getVotingDelegate(sender);
    uint72 finalPropositionBalance2 = getDelegatedPropositionBalance(user);
    uint72 finalVotingBalance2 = getDelegatedVotingBalance(user);

    assert finalVotingDelegate1 == finalVotingDelegate2;
    assert finalPropositionDelegate1 == finalPropositionDelegate2;
    assert finalVotingBalance1 == finalVotingBalance2;
    assert finalPropositionBalance1 == finalPropositionBalance2;
}

rule powerEqualBalanceCondition(address user) {

    mathint balance = balanceOf(user);
    mathint votingPower = getPowerCurrent(user, 0);
    mathint propositionPower = getPowerCurrent(user, 1);
    mathint votingBalance = getDelegatedVotingBalance(user);
    mathint propositionBalance = getDelegatedPropositionBalance(user);
    uint8 delegationState = getDelegationState(user);

    require propositionBalance == 0;
    require votingBalance == 0;
    require delegationState == 0;

    assert votingPower == balance;
    assert propositionPower == balance;    
} 

rule powerAndBalanceRelation(env e, address user) {
    
    uint256 votingPower = getPowerCurrent(user, 0);
    uint256 propositionPower = getPowerCurrent(user, 1);
    uint72 votingBalance = getDelegatedVotingBalance(user);
    uint72 propositionBalance = getDelegatedPropositionBalance(user);
    uint104 aaveBalance = getBalance(user);
    uint8 delegationState = getDelegationState(user);

    assert delegationState == 0 => votingPower == votingBalance * 10^10 + aaveBalance && propositionPower == propositionBalance * 10^10 + aaveBalance;
    assert delegationState == 1 => votingPower == votingBalance * 10^10 && propositionPower == propositionBalance * 10^10 + aaveBalance;
    assert delegationState == 2 => votingPower == votingBalance * 10^10 + aaveBalance && propositionPower == propositionBalance * 10^10;
    assert delegationState == 3 => votingPower == votingBalance * 10^10 && propositionPower == propositionBalance * 10^10;
}


rule delegationToItself(env e, address user) {
    
    require user == e.msg.sender;
    
    mathint initialPropositionBalance = getDelegatedPropositionBalance(user);
    mathint initialVotingBalance = getDelegatedVotingBalance(user);
    mathint initialBalance = balanceOf(user);

    delegate(e, user);

    mathint finalPropositionBalance = getDelegatedPropositionBalance(user);
    mathint finalVotingBalance = getDelegatedVotingBalance(user);
    mathint finalBalance = balanceOf(user);

    assert initialPropositionBalance == finalPropositionBalance;
    assert initialVotingBalance == finalVotingBalance;
    assert initialBalance == finalBalance;
}

rule increaseInPowerOfDelegationByAmountOfSender(env e, address user) {

    address sender = e.msg.sender;
    require sender != 0;
    require user != 0;
    require sender != user;
    
    mathint initialVotingPower = getPowerCurrent(user, 0);
    mathint initialPropositionPower = getPowerCurrent(user, 1);
    mathint initialDelegateState = getDelegationState(user);
    mathint initialVotingBalance = getDelegatedVotingBalance(user);
    mathint initialPropositionBalance = getDelegatedPropositionBalance(user);
    uint104 initialAaveBalance = getBalance(sender);

    require getVotingDelegate(sender) != user;
    require getPropositionDelegate(sender) != user;

    delegateByType(e, user, 0);
    delegateByType(e, user, 1);

    mathint finalVotingPower = getPowerCurrent(user, 0);
    mathint finalPropositionPower = getPowerCurrent(user, 1);
    mathint finalDelegateState = getDelegationState(user);
    mathint finalVotingBalance = getDelegatedVotingBalance(user);
    mathint finalPropositionBalance = getDelegatedPropositionBalance(user);
    uint104 finalAaveBalance = getBalance(sender);

    assert finalVotingPower == initialVotingPower + normalize(finalAaveBalance);
    assert finalPropositionPower == initialPropositionPower + normalize(finalAaveBalance);
    assert finalVotingBalance == initialVotingBalance + finalAaveBalance/10^10;
    assert finalPropositionBalance == initialPropositionBalance + finalAaveBalance/10^10;
    assert initialDelegateState == finalDelegateState;
    assert getVotingDelegate(sender) == user;
    assert getPropositionDelegate(sender) == user;
}


rule addressZeroNoPower(env e) {

    address sender = e.msg.sender;
    address initialPropositionDelegate = getPropositionDelegate(sender);
    address initialVotingDelegate = getVotingDelegate(sender);
    mathint initialPropositionBalance = getDelegatedPropositionBalance(0);
    mathint initialVotingBalance = getDelegatedVotingBalance(0);
    mathint initialBalance = balanceOf(sender);

    require initialVotingDelegate != 0;
    require initialPropositionDelegate != 0;
    require initialVotingBalance == 0;
    require initialPropositionBalance == 0;

    delegate(e, 0);

    mathint finalPropositionBalance = getDelegatedPropositionBalance(0);
    mathint finalVotingBalance = getDelegatedVotingBalance(0);
    mathint finalBalance = balanceOf(sender);

    assert finalVotingBalance == 0;
    assert finalPropositionBalance == 0;
    assert initialBalance == finalBalance;
}

rule propositionDelegateDoesNotAffectOthers(env e, address userA, address userB) {

    address initialVotingDelegate = getVotingDelegate(userA);
    uint104 initialAaveBalance = getBalance(userA);
    delegateByType(e, userB, 1);
    address finalVotingDelegate = getVotingDelegate(userA);
    uint104 finalAaveBalance = getBalance(userA);

    assert initialVotingDelegate == finalVotingDelegate;
    assert initialAaveBalance == finalAaveBalance;
}

rule votingDelegateDoesNotAffectOthers(env e, address userA, address userB) {

    address initialPropositionDelegate = getPropositionDelegate(userA);
    uint104 initialAaveBalance = getBalance(userA);
    delegateByType(e, userB, 0);
    address finalPropositionDelegate = getPropositionDelegate(userA);
    uint104 finalAaveBalance = getBalance(userA);

    assert initialPropositionDelegate == finalPropositionDelegate;
    assert initialAaveBalance == finalAaveBalance;
}

rule changeInDelegateOfUser(env e, method f, calldataarg args, address user) {

    address initialPropositionDelegate = getPropositionDelegate(user);
    address initialVotingDelegate = getVotingDelegate(user);

    f(e, args);

    address finalPropositionDelegate = getPropositionDelegate(user);
    address finalVotingDelegate = getVotingDelegate(user);

    assert (initialPropositionDelegate != finalPropositionDelegate) || (initialVotingDelegate != finalVotingDelegate) => 
    f.selector == delegate(address).selector 
    || f.selector == delegateByType(address,uint8).selector 
    || f.selector == metaDelegate(address,address,uint256,uint8,bytes32,bytes32).selector 
    || f.selector == metaDelegateByType(address,address,uint8,uint256,uint8,bytes32,bytes32).selector;
 }

 rule metaFuncsCanAllowUserToDelegateChanges(env e, method f, calldataarg args, address user) {
    
    address initialVotingDelegate = getVotingDelegate(user);
    address initialPropositionDelegate = getPropositionDelegate(user);
    address sender = e.msg.sender;

    f(e, args);

    address finalVotingDelegate = getVotingDelegate(user);
    address finalPropositionDelegate = getPropositionDelegate(user);

    assert (
        initialVotingDelegate != finalVotingDelegate ||
        initialPropositionDelegate != finalPropositionDelegate
    ) && (
        f.selector != metaDelegate(address,address,uint256,uint8,bytes32,bytes32).selector && 
        f.selector != metaDelegateByType(address,address,uint8,uint256,uint8,bytes32,bytes32).selector 
    ) => sender == user;
}

rule votingPowerStateChange(env e, address user, method f, calldataarg args, address from, address to, uint256 amount) {
    mathint initialVotingPower = getPowerCurrent(user, 0);

    if(f.selector == transfer(address,uint256).selector) {
        transfer(e, to, amount);
    } else if(f.selector == transferFrom(address,address,uint256).selector) {
        transferFrom(e, from, to, amount);
    } else {
        f(e, args);
    }

    mathint finalVotingPower = getPowerCurrent(user, 0);

    assert finalVotingPower > 0 && initialVotingPower == 0 => balanceOf(user) > 0 || getVotingDelegate(e.msg.sender) == user ||
    getVotingDelegate(to) == user || f.selector == metaDelegate(address,address,uint256,uint8,bytes32,bytes32).selector ||
        f.selector == metaDelegateByType(address,address,uint8,uint256,uint8,bytes32,bytes32).selector;
}

invariant addressZeroDoesNotHaveVotingPower()
    getBalance(0) == 0 && getPowerCurrent(0, 0) == 0

invariant addressZeroDoesNotHavePropositionPower()
    getBalance(0) == 0 && getPowerCurrent(0, 1) == 0



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