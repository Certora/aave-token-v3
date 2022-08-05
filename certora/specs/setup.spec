/**

    Setup for writing rules for Aave Token v3 

*/

using AaveTokenV3 as token


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
    getPowersCurrent(address user) returns (uint256, uint256) envfree
    getBalance(address user) returns (uint104) envfree
    getDelegatedPropositionBalance(address user) returns (uint72) envfree
    getDelegatedVotingBalance(address user) returns (uint72) envfree
    getDelegatingProposition(address user) returns (bool) envfree
    getDelegatingVoting(address user) returns (bool) envfree
    getVotingDelegate(address user) returns (address) envfree
    getPropositionDelegate(address user) returns (address) envfree
    getNoDelegation(address user) returns (bool) envfree
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


// -----------------------------------------------------------------------------------------------------------------
/**

    Check that delegation cannot be changed by functions other than the ones that are supposed to

*/

rule delegateCannotBeChangedByOtherFunctions(method f, address delegator, address delegatee) {
    env e;
    calldataarg args;
    address delegateeVotingBefore; address delegateePropositionBefore;
    delegateeVotingBefore, delegateePropositionBefore = getDelegates(e, delegator);
    f(e, args);
    address delegateeVotingAfter; address delegateePropositionAfter;
    delegateeVotingAfter, delegateePropositionAfter = getDelegates(e, delegator);

    assert (f.selector != metaDelegateByType(address,address,uint8,uint256,uint8,bytes32,bytes32).selector && f.selector != delegateByType(address, token.GovernancePowerType).selector && f.selector != delegate(address).selector && f.selector != metaDelegate(address,address,uint256,uint8,bytes32,bytes32).selector ) 
    => (delegateeVotingBefore == delegateeVotingAfter && delegateePropositionBefore == delegateePropositionAfter), "Delegate changed";
}

/**
    Checks that the correct user is delegated for the right type - voting 
*/

rule checkIfCorrectUserIsDelegated(address delegatee) {
    env e;
    calldataarg args;
    address delegator = e.msg.sender;
    address currentDelegatee = getDelegateeByType(e, delegator, VOTING_POWER());
    delegateByType(e, delegatee, VOTING_POWER());
    address newDelegatee = getDelegateeByType(e, delegator, VOTING_POWER());
    require currentDelegatee != delegatee;
    assert (delegatee != delegator) => newDelegatee == delegatee, "Wrong delgatee delegated";
}


/**
    Checks that the correct user is delegated for the right type - proposition 
*/

rule checkIfUserHasCorrectDelegationType(address delegator, address delegatee) {
    env e;
    calldataarg args;
    require delegator == e.msg.sender;
    address currentDelegatee = getDelegateeByType(e, delegator, PROPOSITION_POWER());
    require currentDelegatee != delegatee && delegator != delegatee;
    delegateByType(e, delegatee, PROPOSITION_POWER());
    address newDelegatee = getDelegateeByType(e, delegator, PROPOSITION_POWER());

    assert newDelegatee == delegatee, "Wrong delgatee delegated";
}

/**
    Transfer function changes balance accordingly
*/

rule transferChangesBalanceAccordingly(uint256 amount, address user) {
    env e;
    address owner = e.msg.sender;
    uint256 balanceBefore = balanceOf(owner);
    address delegateeVotingBefore; address delegateePropositionBefore;
    delegateeVotingBefore, delegateePropositionBefore = getDelegates(e, owner);    
    require owner != user;
    transfer(e, user, amount);
    uint256 balanceAfter = balanceOf(owner);
    assert balanceAfter == balanceBefore - amount, "Wrong change in Balance ";
}

/** 
    Transfer function cannot transfer power to user with DelegationState.NO_DELEGATION 

*/

rule transferDelegationOnlyToDelegable(uint256 amount, address user) {
    env e;
    require user != e.msg.sender && user != 0;
    address owner = e.msg.sender;

    require (getDelegatingVoting(user) && getDelegatingProposition(user)) == false;
    require owner != user;

    address delegateeVotingBefore; address delegateePropositionBefore;
    delegateeVotingBefore, delegateePropositionBefore = getDelegates(e, owner);     

    // User is not a previous delegatee of the owner    
    require delegateeVotingBefore != user;
    require delegateePropositionBefore != user;

    transfer(e, user, amount);

    address delegateeVoting; address delegateeProposition;
    delegateeVoting, delegateeProposition = getDelegates(e, owner);
    assert delegateeVoting != user, "NO_DELEGATION state user gets delegated in transfer";
}

/**
    check for user own power only. Then delegate & check for increased power 
*/

/** 
    Change user from NoDelegation to Delegating
*/

rule fromNoDelegationToDelegate(address user) {
    env e;
    uint256 userVotingPower;
    address owner = e.msg.sender;
    require user != 0;
    require(getNoDelegation(owner));
    require owner != user;

    // make sure the owner has balance
    require getBalance(owner) >0;
    // Make sure the user is not already a delegatee
    address currentDelegatee = getDelegateeByType(e, owner, VOTING_POWER());
    require currentDelegatee != user;
    require currentDelegatee == 0;
    require(getDelegatedVotingBalance(owner) > 0);

    delegateByType(e, user, 0);

    assert getNoDelegation(owner) == false, "DelegationState has not changed";
}

/**
    Transfer of tokens between users who are not delegating power
*/

rule transferOfTokensBetweenNoDelegationUserVoting(address user, uint256 amount) {
    env e;
    address owner = e.msg.sender;
    require user != 0;
    require owner != user;
    require getBalance(owner) >0;
    require (getNoDelegation(owner));
    require (getNoDelegation(user));

    uint256 ownerVotingPower; uint256 ownerPropositionPower;    
    ownerVotingPower, ownerPropositionPower = getPowersCurrent(owner);
    uint256 userVotingPower; uint256 userPropositionPower;
    userVotingPower, userPropositionPower = getPowersCurrent(user);

    transfer(e, user, amount);

    uint256 ownerVotingPowerAfter; uint256 ownerPropositionPowerAfter;    
    ownerVotingPowerAfter, ownerPropositionPowerAfter = getPowersCurrent(owner);
    uint256 userVotingPowerAfter; uint256 userPropositionPowerAfter;    
    userVotingPowerAfter, userPropositionPowerAfter = getPowersCurrent(user);

    assert (ownerVotingPowerAfter == ownerVotingPower - amount) && 
    (userVotingPowerAfter == userVotingPower + amount) , "VotingPower is not accurate";
    assert (ownerPropositionPowerAfter == ownerPropositionPower - amount) && 
    (userPropositionPowerAfter == userPropositionPower + amount) , "Proposition Power is not accurate";    
}

/**
     NoDelegation user1 delegates to another user2, user1 power changes accordingly
*/

rule noDelegationDelegatesPower(address user) {
    env e;
    address owner = e.msg.sender;
    require user != 0;
    require owner != user;
    uint256 ownerBalance = getBalance(owner);
    require ownerBalance > 0;
    require (getNoDelegation(owner)); 
    address ownerDelegatee = getDelegateeByType(e, owner, VOTING_POWER());
    require ownerDelegatee == 0;
    uint256 ownerVotingPower; uint256 ownerPropositionPower;    
    ownerVotingPower, ownerPropositionPower = getPowersCurrent(owner);
    uint256 userVotingPower; uint256 userPropositionPower;
    userVotingPower, userPropositionPower = getPowersCurrent(user);  

    delegate(e, user);

    uint256 ownerVotingPowerAfter; uint256 ownerPropositionPowerAfter;    
    ownerVotingPowerAfter, ownerPropositionPowerAfter = getPowersCurrent(owner);
    uint256 userVotingPowerAfter; uint256 userPropositionPowerAfter;    
    userVotingPowerAfter, userPropositionPowerAfter = getPowersCurrent(user);

    address ownerDelegateeAfter = getDelegateeByType(e, owner, VOTING_POWER());

    assert (ownerVotingPowerAfter == ownerVotingPower - ownerBalance) && 
    (ownerPropositionPowerAfter == ownerPropositionPower - ownerBalance); 
    assert (ownerDelegateeAfter == user );
}



/**
     NoDelegation user1 delegates to another user2, user2 power changes accordingly
*/

rule noDelegationDelegatesPowerChanges(address user) {
    env e;
    address owner = e.msg.sender;
    require user != 0;
    require owner != user;
    uint256 ownerBalance = getBalance(owner);
    require ownerBalance > 0;
    require (getNoDelegation(owner)); 
    address ownerDelegatee = getDelegateeByType(e, owner, VOTING_POWER());
    require ownerDelegatee == 0;
    uint256 ownerVotingPower; uint256 ownerPropositionPower;    
    ownerVotingPower, ownerPropositionPower = getPowersCurrent(owner);
    uint256 userVotingPower; uint256 userPropositionPower;
    userVotingPower, userPropositionPower = getPowersCurrent(user);  

    delegate(e, user);

    uint256 ownerVotingPowerAfter; uint256 ownerPropositionPowerAfter;    
    ownerVotingPowerAfter, ownerPropositionPowerAfter = getPowersCurrent(owner);
    uint256 userVotingPowerAfter; uint256 userPropositionPowerAfter;    
    userVotingPowerAfter, userPropositionPowerAfter = getPowersCurrent(user);

    address ownerDelegateeAfter = getDelegateeByType(e, owner, VOTING_POWER());

 
    assert (userVotingPowerAfter == userVotingPower + normalize(ownerBalance)) && 
    (userPropositionPowerAfter == userPropositionPower + normalize(ownerBalance));
    assert (ownerDelegateeAfter == user );
}
/**
     Delegating account transfers tokens to another delegating account. Their Powers & change 
     in their delegatee powers are checked accordinly
*/
rule delegatingAccountTransferTokens(address bob, uint256 amount) {
    env e;
    address alice = e.msg.sender;
    require bob != 0;
    require alice != bob;
    uint256 aliceBalance = getBalance(alice);
    uint256 bobBalance = getBalance(bob);

    require aliceBalance > 0;
    require getNoDelegation(alice) == false;
    uint256 aliceVotingPower; uint256 bobVotingPower;
    require (getDelegatedVotingBalance(alice) == 0);
    require (getDelegatedVotingBalance(bob) == 0);
    aliceVotingPower = getPowerCurrent(alice, VOTING_POWER());
    bobVotingPower = getPowerCurrent(bob, VOTING_POWER());

    address aliceDelegatee = getDelegateeByType(e, alice, VOTING_POWER());
    address bobDelegatee = getDelegateeByType(e, bob, VOTING_POWER());
    require (aliceDelegatee != bobDelegatee && aliceDelegatee != 0 && bobDelegatee != 0);
    uint256 aliceDelegateePower = getPowerCurrent(aliceDelegatee, VOTING_POWER());
    uint256 bobDelegateePower = getPowerCurrent(bobDelegatee, VOTING_POWER());

    transfer(e, bob, amount);

    uint256 aliceBalanceAfter = getBalance(alice);
    uint256 bobBalanceAfter = getBalance(bob);

    uint256 aliceDelegateePowerAfter = getPowerCurrent(aliceDelegatee, VOTING_POWER());
    uint256 bobDelegateePowerAfter = getPowerCurrent(bobDelegatee, VOTING_POWER());    

    assert (aliceVotingPower == 0 && bobVotingPower == 0) && (aliceDelegateePowerAfter == aliceDelegateePower - normalize(aliceBalance) + normalize(aliceBalanceAfter)) &&
    ((bobDelegateePowerAfter == bobDelegateePower - normalize(bobBalance) + normalize(bobBalanceAfter))), "Delagatee Balances are not accurate";
}

/**
     Non-Delegating account transfers tokens to another delegating account. Their Powers & change 
     in their delegatee powers are checked accordinly    
*/

rule nonDelAccountToDelAccountTransferA(address bob, uint256 amount) {
    env e;
    address alice = e.msg.sender;
    require bob != 0;
    require alice != bob;
    uint256 aliceBalance = getBalance(alice);
    require (getNoDelegation(alice)); 

    require aliceBalance > 0;
    require getNoDelegation(bob) == false;    
    uint256 aliceVotingPower; uint256 bobVotingPower;
    aliceVotingPower = getPowerCurrent(alice, VOTING_POWER());
    bobVotingPower = getPowerCurrent(bob, VOTING_POWER());

    address aliceDelegatee = getDelegateeByType(e, alice, VOTING_POWER());
    address bobDelegatee = getDelegateeByType(e, bob, VOTING_POWER());
    require (aliceDelegatee != bobDelegatee && aliceDelegatee != 0 && bobDelegatee != 0);

    transfer(e, bob, amount);

    uint256 aliceVotingPowerAfter = getPowerCurrent(alice, VOTING_POWER());

    assert (aliceVotingPowerAfter == aliceVotingPower - amount && bobVotingPower == 0), "Voting powers for accounts are not accurate";
}


rule nonDelAccountToDelAccountTransferB(address bob, uint256 amount) {
    env e;
    address alice = e.msg.sender;
    require bob != 0;
    require alice != bob;
    uint256 aliceBalance = getBalance(alice);
    uint256 bobBalance = getBalance(bob);
    require (getNoDelegation(alice)); 

    require aliceBalance > 0;
    require getNoDelegation(bob) == false;    

    address aliceDelegatee = getDelegateeByType(e, alice, VOTING_POWER());
    address bobDelegatee = getDelegateeByType(e, bob, VOTING_POWER());
    require (aliceDelegatee != bobDelegatee && aliceDelegatee != 0 && bobDelegatee != 0);
    uint256 aliceDelegateePower = getPowerCurrent(aliceDelegatee, VOTING_POWER());
    uint256 bobDelegateePower = getPowerCurrent(bobDelegatee, VOTING_POWER());

    transfer(e, bob, amount);

    uint256 aliceBalanceAfter = getBalance(alice);
    uint256 bobBalanceAfter = getBalance(bob);

    uint256 aliceDelegateePowerAfter = getPowerCurrent(aliceDelegatee, VOTING_POWER());
    uint256 bobDelegateePowerAfter = getPowerCurrent(bobDelegatee, VOTING_POWER());    

    assert ((aliceDelegateePowerAfter == aliceDelegateePower - normalize(aliceBalance) + normalize(aliceBalanceAfter)) &&
    ((bobDelegateePowerAfter == bobDelegateePower - normalize(bobBalance) + normalize(bobBalanceAfter)))), "Delagatee Balances are not accurate";
}

/**
    Delegatee Power after delegation is revoked. Check for delegator power increase & 
    check for decrease in delegatee power
*/

rule delegateePowerAfterStopDelegatingA() {
    env e;
    address alice = e.msg.sender;

    uint256 aliceBalance = getBalance(alice);
    require aliceBalance > 0;

    require getNoDelegation(alice) == false;    
    uint256 aliceVotingPower; 
    aliceVotingPower = getPowerCurrent(alice, VOTING_POWER());
    address aliceDelegatee = getDelegateeByType(e, alice, VOTING_POWER());
    require aliceDelegatee != 0 && alice != aliceDelegatee;

    // Self delegate to remove delagation
    delegate(e, alice);

    uint256 aliceVotingPowerAfter = getPowerCurrent(alice, VOTING_POWER());

    assert (aliceVotingPowerAfter == aliceVotingPower + aliceBalance ), "Delegator balance update incorrect"; 
}

rule delegateePowerAfterStopDelegatingB() {
    env e;
    address alice = e.msg.sender;

    uint256 aliceBalance = getBalance(alice);
    require aliceBalance > 0;

    require getNoDelegation(alice) == false;    
    uint256 aliceVotingPower; 
    address aliceDelegatee = getDelegateeByType(e, alice, VOTING_POWER());
    uint256 aliceDelegateePower = getPowerCurrent(aliceDelegatee, VOTING_POWER());
    require aliceDelegatee != 0 && alice != aliceDelegatee;

    // Self delegate to remove delagation
    delegate(e, alice);

    uint256 aliceDelegateePowerAfter = getPowerCurrent(aliceDelegatee, VOTING_POWER());

    assert aliceDelegateePowerAfter == (aliceDelegateePower - normalize(aliceBalance)), "Delegation Powers after removing delegation is incorrect";
}

// completed
// Transfer of delegation
/**
    Already delegating user when delegates, their power remains zero. 
    Delegatee power changes accordingly
*/
rule transferOfDelegationA(address bob) {
    env e;
    address alice = e.msg.sender;

    uint256 aliceBalance = getBalance(alice);
    require aliceBalance > 0; 
    require getNoDelegation(alice) == false;    

    require (getDelegatedVotingBalance(alice) == 0);
    uint256 aliceVotingPower; 
    aliceVotingPower = getPowerCurrent(alice, VOTING_POWER());
    address aliceDelegatee = getDelegateeByType(e, alice, VOTING_POWER());
    require aliceDelegatee != 0 && alice != aliceDelegatee && bob != 0 
    && alice != bob && aliceDelegatee != bob;

    uint256 bobPower = getPowerCurrent(bob, VOTING_POWER());    

    delegate(e, bob);
    
    uint256 bobPowerAfter = getPowerCurrent(bob, VOTING_POWER());    
    uint256 aliceVotingPowerAfter = getPowerCurrent(alice, VOTING_POWER());

    assert (aliceVotingPowerAfter == 0 && aliceVotingPower ==  0), "Voting power should be zero if delegating";
}

rule transferOfDelegationB(address bob) {
    env e;
    address alice = e.msg.sender;

    uint256 aliceBalance = getBalance(alice);
    require aliceBalance > 0; 
    require getNoDelegation(alice) == false;    

    require (getDelegatedVotingBalance(alice) == 0);
    uint256 aliceVotingPower; 
    address aliceDelegatee = getDelegateeByType(e, alice, VOTING_POWER());
    uint256 aliceDelegateePower = getPowerCurrent(aliceDelegatee, VOTING_POWER());
    require aliceDelegatee != 0 && alice != aliceDelegatee && bob != 0 
    && alice != bob && aliceDelegatee != bob;
    uint256 bobPower = getPowerCurrent(bob, VOTING_POWER());    

    delegate(e, bob);
    
    uint256 aliceDelegateePowerAfter = getPowerCurrent(aliceDelegatee, VOTING_POWER());    
    uint256 bobPowerAfter = getPowerCurrent(bob, VOTING_POWER());    

    assert ((aliceDelegateePowerAfter == aliceDelegateePower - normalize(aliceBalance)) &&  (bobPowerAfter == bobPower + normalize(aliceBalance))), "Power transfer is incorrect";
}

/**
    Only Delegator can change their delegatee
*/

rule onlyDelegatorCanChangeDelegatee(method f, address alice) {
    env e;

    address aliceVotingDelegatee = getDelegateeByType(e, alice, VOTING_POWER());
    require getNoDelegation(alice) == false;    
    require aliceVotingDelegatee != 0 && alice != aliceVotingDelegatee;

    require e.msg.sender != alice;
    // checkForMetaDelegate(e, f, alice);
    if (f.selector == metaDelegate(address, address, uint256, uint8, bytes32, bytes32).selector) {
        address delegator; address other; uint256 t; uint8 v; bytes32 r; bytes32 s;
        require delegator != alice;
        metaDelegate(e, delegator, other, t, v ,r, s);
    }
    else if (f.selector == metaDelegateByType(address,address,uint8,uint256,uint8,bytes32,bytes32).selector) {
        address delegator; address other; uint256 t; uint8 v; bytes32 r; bytes32 s;
        require delegator != alice;
        metaDelegateByType(e, delegator, other, VOTING_POWER(), t, v ,r, s);
    }        
    else {
        calldataarg args;
        f(e, args);
    }     

    address aliceVotingDelegateeAfter = getDelegateeByType(e, alice, VOTING_POWER());

    assert aliceVotingDelegateeAfter == aliceVotingDelegatee, "Delegatee cannot be changed by others";
}

/**
    Change in one type of delegation does not affect the other type 
*/
rule changeInPropositionNoEffectOnVoting(method f, address bob) filtered {
    f -> f.selector != delegate(address).selector && 
    f.selector != metaDelegate(address,address,uint256,uint8,bytes32,bytes32).selector &&
    f.selector != transfer(address,uint256).selector && 
    f.selector != transferFrom(address,address,uint256).selector &&
    f.selector != _governancePowerTransferByType(uint104,uint104,address,uint8).selector
} {
    env e;

    address alice = e.msg.sender;
    require alice != 0 && bob != 0 && bob != alice;
    require getNoDelegation(alice) == false;    
    address aliceVotingDelegatee = getDelegateeByType(e, alice, VOTING_POWER());
    require aliceVotingDelegatee != 0 && alice != aliceVotingDelegatee;
    uint72 aliceVotingBalance = getDelegatedVotingBalance(aliceVotingDelegatee);

    // delegateByType(e, alice, PROPOSITION_POWER());
    if (f.selector == metaDelegateByType(address,address,uint8,uint256,uint8,bytes32,bytes32).selector) {
        uint256 t; uint8 v; bytes32 r; bytes32 s;
        metaDelegateByType(e, alice, bob, PROPOSITION_POWER(), t, v ,r, s);
    } else if (f.selector == delegateByType(address, token.GovernancePowerType).selector) {
        delegateByType(e, bob, PROPOSITION_POWER());
    }
    else {
        calldataarg args;
        f(e, args);
    }

    address aliceVotingDelegateeAfter = getDelegateeByType(e, alice, VOTING_POWER());
    uint72 aliceVotingBalanceAfter = getDelegatedVotingBalance(aliceVotingDelegateeAfter); 

    assert (aliceVotingBalanceAfter == aliceVotingBalance && aliceVotingDelegateeAfter == aliceVotingDelegatee);
    // (f.selector != delegate(address).selector && f.selector != metaDelegate(address,address,uint256,uint8,bytes32,bytes32).selector), "Doesnt work";
}

/**
    A user balance changes only in transfer & transferFrom funcitons
*/

rule balanceUnaffectedInOtherFunctions(method f) filtered {
    f -> f.selector != transfer(address,uint256).selector && 
    f.selector != transferFrom(address,address,uint256).selector } 
{
    env e; 
    calldataarg args;
    address alice = e.msg.sender;
    uint104 aliceBalance = getBalance(alice);

    f(e, args);

    uint104 aliceBalanceAfter = getBalance(alice);
    
    assert aliceBalanceAfter == aliceBalance, "Balance has changed";
}

/**
    If a user balance is zero then the power delegated to the delegatee is same as previous value
*/
rule zeroBalanceCannotAddToDelegatedBalance(address bob) {
    env e;

    address alice = e.msg.sender;

    uint256 aliceBalance = getBalance(alice);
    require aliceBalance == 0;
    // require (getVotingDelegate(alice) == bob && getPropositionDelegate(alice) == bob);
    uint256 bobVotingBalance = getDelegatedVotingBalance(bob);
    
    delegate(e, bob);

    uint256 bobVotingBalanceAfter = getDelegatedVotingBalance(bob);

    assert bobVotingBalanceAfter == bobVotingBalance, "Voting Balance cannot change";
    
}

/**
    If an account delegates power to itself or the zero address, that account is not delegating power to anyone
*/

rule noDelegateeAfterDelegateToZero() {
    env e;
    address alice = e.msg.sender;
    address aliceDelegatee = getVotingDelegate(alice);
    require aliceDelegatee != 0;
    require getDelegatingVoting(alice);
    delegate(e, 0);

    address aliceDelegateeAfter = getVotingDelegate(alice);

    assert aliceDelegateeAfter == 0, "Delegatee not set to zero";
}

/**
    An account cannot delegate power that has been delegated to it from another account 
*/

rule delegatedAccountCannotTransferDelegatedBalance(address bob) {
    env e;

    address alice = e.msg.sender;
    address aliceDelegatee = getDelegateeByType(e, alice, VOTING_POWER());
    require aliceDelegatee != 0 && aliceDelegatee != alice && aliceDelegatee != bob;
    uint256 aliceVotingBalance = getDelegatedVotingBalance(alice);
    require aliceVotingBalance > 0;
    
    delegate(e, bob);

    uint256 aliceVotingBalanceAfter = getDelegatedVotingBalance(alice);

    assert aliceVotingBalanceAfter == aliceVotingBalance, "Voting Balance cannot change";
}
