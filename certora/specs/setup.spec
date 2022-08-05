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
    --------------------------------------------------------
    --------------------------------------------------------
                   Below are the new rules
    --------------------------------------------------------
    --------------------------------------------------------
*/

/**

    Verify that only delegate functions can change someone's delegate.

*/

rule votingDelegateChanges_updated(address alice, method f) {
    env e;
    calldataarg args;

    address aliceVotingDelegateBefore = getVotingDelegate(alice);
    address alicePropositionDelegateBefore = getPropositionDelegate(alice);

    f(e, args);

    address aliceVotingDelegateAfter = getVotingDelegate(alice);
    address alicePropositionDelegateAfter = getPropositionDelegate(alice);

    // only these four function may change the delegate of an address
    assert (aliceVotingDelegateAfter != aliceVotingDelegateBefore) ||  (alicePropositionDelegateBefore != alicePropositionDelegateAfter) =>
        f.selector == delegate(address).selector || 
        f.selector == delegateByType(address,uint8).selector ||
        f.selector == metaDelegate(address,address,uint256,uint8,bytes32,bytes32).selector ||
        f.selector == metaDelegateByType(address,address,uint8,uint256,uint8,bytes32,bytes32).selector;
}

/**

    Integrity of delegate():
        - Adds delegator balance to delegatee voting & proposing power
        - Updates voting delegate


*/

rule integrityOfDdelegate(address bob, method f) filtered {
        f -> 
        f.selector == delegate(address).selector || 
        f.selector == metaDelegate(address,address,uint256,uint8,bytes32,bytes32).selector
}{
    env e;
    calldataarg args;

    address delegator;
    uint256 deadline;
    uint8 v;
    bytes32 r;
    bytes32 s;

    // delegate not to self or to zero
    require bob != e.msg.sender && bob != delegator && bob != 0;

    // avoid unrealistic delegated balance
    require(getDelegatedVotingBalance(bob) < MAX_DELEGATED_BALANCE());
    require(getDelegatedPropositionBalance(bob) < MAX_DELEGATED_BALANCE());
    
    uint256 bobVotingPowerBefore = getPowerCurrent(bob, VOTING_POWER());
    uint256 bobPropositionPowerBefore = getPowerCurrent(bob, PROPOSITION_POWER());

    // Var declaration with initial value
    uint256 delegatorBalance = 0;
    address delegatorAddress = 0x0;

    if (f.selector == delegate(address).selector){
        delegatorAddress = e.msg.sender;
    } else if (f.selector == metaDelegate(address,address,uint256,uint8,bytes32,bytes32).selector){
        delegatorAddress = delegator;
    }

    bool votingDelegateWasNotBob = getVotingDelegate(delegatorAddress) != bob;
    bool propositionDelegateWasNotBob = getPropositionDelegate(delegatorAddress) != bob;
    delegatorBalance = balanceOf(delegatorAddress);        

    if (f.selector == delegate(address).selector) {
        delegate(e, bob);
    } else if (f.selector == metaDelegate(address,address,uint256,uint8,bytes32,bytes32).selector) {
        metaDelegate(e, delegator, bob, deadline, v, r, s);
    } 
    // Have to leave else branch otherwise there will be a error
    else {
        f(e, args);
    }

    // test the delegate indeed is now bob
    assert bob == getVotingDelegate(delegatorAddress);
    assert bob == getPropositionDelegate(delegatorAddress);  

    // test the delegate's new voting power
    uint256 bobVotingPowerAfter = getPowerCurrent(bob, VOTING_POWER());
    assert votingDelegateWasNotBob => bobVotingPowerAfter == bobVotingPowerBefore + normalize(delegatorBalance);

    // test the delegate's new proposition power
    uint256 bobPropositionPowerAfter = getPowerCurrent(bob, PROPOSITION_POWER());
    assert propositionDelegateWasNotBob => bobPropositionPowerAfter == bobPropositionPowerBefore + normalize(delegatorBalance);
}

/**

    Integrity of delegateByType():
        - Invalid governance type will not change voting, proposition power and delegate
        - Adds delegator balance to delegatee voting or proposing power
        - It shall not influence the other power

*/

rule integrityOfDdelegateByType(address bob, method f) filtered {
        f -> 
        f.selector == delegateByType(address,uint8).selector ||
        f.selector == metaDelegateByType(address,address,uint8,uint256,uint8,bytes32,bytes32).selector
}{
    env e;
    calldataarg args;
    uint8 governanceType;

    address delegator;
    uint256 deadline;
    uint8 v;
    bytes32 r;
    bytes32 s;

    // delegate not to self or to zero
    require bob != e.msg.sender && bob != delegator && bob != 0;

    // avoid unrealistic delegated balance
    require(getDelegatedVotingBalance(bob) < MAX_DELEGATED_BALANCE());
    require(getDelegatedPropositionBalance(bob) < MAX_DELEGATED_BALANCE());
    
    uint256 bobVotingPowerBefore = getPowerCurrent(bob, VOTING_POWER());
    uint256 bobPropositionPowerBefore = getPowerCurrent(bob, PROPOSITION_POWER());

    // Var declaration with initial value
    uint256 delegatorBalance = 0;
    address delegatorAddress = 0x0;

    if (f.selector == delegateByType(address,uint8).selector){
        delegatorAddress = e.msg.sender;
    } else if (f.selector == metaDelegateByType(address,address,uint8,uint256,uint8,bytes32,bytes32).selector){
        delegatorAddress = delegator;
    }

    address votingDelegateBefore = getVotingDelegate(delegatorAddress);
    address propositionDelegateBefore = getPropositionDelegate(delegatorAddress);

    bool votingDelegateWasNotBob = votingDelegateBefore != bob;
    bool propositionDelegateWasNotBob = propositionDelegateBefore != bob;
    delegatorBalance = balanceOf(delegatorAddress);        

    if (f.selector == delegateByType(address,uint8).selector) {
        delegateByType(e, bob, governanceType);
    } else if (f.selector == metaDelegateByType(address,address,uint8,uint256,uint8,bytes32,bytes32).selector) {
        metaDelegateByType(e, delegator, bob, governanceType, deadline, v, r, s);
    } 
    // Have to leave else branch otherwise there will be a error
    else {
        f(e, args);
    }


    uint256 bobVotingPowerAfter = getPowerCurrent(bob, VOTING_POWER());
    uint256 bobPropositionPowerAfter = getPowerCurrent(bob, PROPOSITION_POWER());

    // Invalid governance type will not change voting, proposition power and delegate
    assert governanceType != VOTING_POWER() && governanceType != PROPOSITION_POWER() =>
        bobVotingPowerAfter == bobVotingPowerBefore && bobPropositionPowerAfter == bobPropositionPowerBefore &&
        votingDelegateBefore == getVotingDelegate(delegatorAddress) && propositionDelegateBefore == getPropositionDelegate(delegatorAddress);

    // test the delegate indeed is now bob and did not change other voting type delegate
    assert governanceType == VOTING_POWER() => bob == getVotingDelegate(delegatorAddress);
    assert governanceType == PROPOSITION_POWER() => bob == getPropositionDelegate(delegatorAddress);

    // test the delegate's new voting power and proposition power
    assert votingDelegateWasNotBob && governanceType == VOTING_POWER() => (bobVotingPowerAfter == bobVotingPowerBefore + normalize(delegatorBalance)) && 
        bobPropositionPowerAfter == bobPropositionPowerBefore;

    // test the delegate's new proposition power and voting power
    assert propositionDelegateWasNotBob && governanceType == PROPOSITION_POWER() => (bobPropositionPowerAfter == bobPropositionPowerBefore + normalize(delegatorBalance)) && 
        bobVotingPowerAfter == bobVotingPowerBefore;
}

/**

    Testing correctness of delegating voting power

*/

rule delegateCorrectness_updated(address bob, method f) filtered {
        f -> 
        f.selector == delegate(address).selector || 
        f.selector == delegateByType(address,uint8).selector ||
        f.selector == metaDelegate(address,address,uint256,uint8,bytes32,bytes32).selector || 
        f.selector == metaDelegateByType(address,address,uint8,uint256,uint8,bytes32,bytes32).selector
}{
    env e;
    calldataarg args;

    address delegator;
    uint256 deadline;
    uint8 v;
    bytes32 r;
    bytes32 s;

    // delegate not to self or to zero
    require bob != e.msg.sender && bob != delegator && bob != 0;

    uint256 bobDelegatedBalance = getDelegatedVotingBalance(bob);
    // avoid unrealistic delegated balance
    require(bobDelegatedBalance < MAX_DELEGATED_BALANCE());
    
    uint256 bobVotingPowerBefore = getPowerCurrent(bob, VOTING_POWER());
    uint256 bobPropositionPowerBefore = getPowerCurrent(bob, PROPOSITION_POWER());

    // Var declaration with initial value
    uint256 delegatorBalance = 0;
    address delegatorAddress = 0x0;

    if (f.selector == delegate(address).selector || 
        f.selector == delegateByType(address,uint8).selector) {
        
        delegatorAddress = e.msg.sender;
    } else if (f.selector == metaDelegate(address,address,uint256,uint8,bytes32,bytes32).selector || 
               f.selector == metaDelegateByType(address,address,uint8,uint256,uint8,bytes32,bytes32).selector) {
        
        delegatorAddress = delegator;
    }

    // filter that the delegator doesn't already delegate to bob
    require getVotingDelegate(delegatorAddress) != bob;
    delegatorBalance = balanceOf(delegatorAddress);        

    if (f.selector == delegate(address).selector || 
        f.selector == delegateByType(address,uint8).selector) {

        if (f.selector == delegate(address).selector) {
            delegate(e, bob);
        } else {
            delegateByType(e, bob, VOTING_POWER());
        }

    } else if (f.selector == metaDelegate(address,address,uint256,uint8,bytes32,bytes32).selector || 
               f.selector == metaDelegateByType(address,address,uint8,uint256,uint8,bytes32,bytes32).selector) {

        if (f.selector == metaDelegate(address,address,uint256,uint8,bytes32,bytes32).selector) {
            metaDelegate(e, delegator, bob, deadline, v, r, s);
        } else { 
            metaDelegateByType(e, delegator, bob, VOTING_POWER(), deadline, v, r, s);
        }
    } 
    // Have to leave else branch otherwise there will be a error
    else {
        f(e, args);
    }

    // test the delegate indeed is now bob
    assert bob == getVotingDelegate(delegatorAddress); 

    // test the delegate's new voting power
    uint256 bobVotingPowerAfter = getPowerCurrent(bob, VOTING_POWER());
    //assert bobVotingPowerAfter == bobVotingPowerBefore + normalize(msgSenderBalance);
    assert bobVotingPowerAfter == bobVotingPowerBefore + normalize(delegatorBalance);

}




/**

    State transition from not having a voting power to having a voting power
        One has voting power when:
            balanceOf(user) > 0
            User has been delegated power

    sh certora/scripts/setup.sh stateTransitionToVotingPower withTransferFromAndDelegate
*/

rule stateTransitionToVotingPower(address bob, method f){
    // We are not testing _governancePowerTransferByType() because function is public only in Harness contract 
    //     and AaveTokenV3 has function defined as a internal.
    require(f.selector != _governancePowerTransferByType(uint104,uint104,address,uint8).selector);

    env e;
    calldataarg args;
    address to;
    address from;
    uint256 amount;
    uint8 governanceType;

    uint256 deadline;
    uint8 v;
    bytes32 r;
    bytes32 s;

    uint256 bobVotingPowerBefore = getPowerCurrent(bob, VOTING_POWER());
    uint256 bobBalanceBefore = balanceOf(bob);

    if (f.selector == transfer(address,uint256).selector){
        transfer(e,to,amount);
    } else if (f.selector == transferFrom(address,address,uint256).selector){
        transferFrom(e,from,to,amount);
    } else if (f.selector == delegateByType(address,uint8).selector) {
        delegateByType(e, bob, governanceType);
    } else if (f.selector == metaDelegate(address,address,uint256,uint8,bytes32,bytes32).selector) {
        metaDelegate(e, from, bob, deadline, v, r, s);
    } else if (f.selector == metaDelegateByType(address,address,uint8,uint256,uint8,bytes32,bytes32).selector) {
        metaDelegateByType(e, to, bob, governanceType, deadline, v, r, s);
    } else {
        f(e, args);
    }
    
    uint256 bobVotingPowerAfter = getPowerCurrent(bob, VOTING_POWER());
    uint256 bobBalanceAfter = balanceOf(bob);

    bool hasVotingPowerBefore = bobVotingPowerBefore > 0;
    bool hasVotingPowerAfter = bobVotingPowerAfter > 0;

    assert !hasVotingPowerBefore && hasVotingPowerAfter => (
        (bobBalanceBefore == 0 && bobBalanceAfter > 0) || 
        (bobBalanceBefore > 0 && from == bob) || 
        (e.msg.sender == bob && bobBalanceBefore > 0) || 
        (getVotingDelegate(to) == bob || to == bob && balanceOf(to) > 0) || 
        (getVotingDelegate(e.msg.sender) == bob && balanceOf(e.msg.sender) > 0) ||
        (getVotingDelegate(from) == bob && balanceOf(from) > 0));
}



/**

    State transition
        One stops having voting power when:
            They delegate to another account and they have not been delegated-to
            They weren't delegating and transferred all their funds

*/

/*
did not yet finish
rule stateTransitionStopsHavingVotingPower(address bob, method f){
    // We are not testing _governancePowerTransferByType() because function is public only in Harness contract 
    //     and AaveTokenV3 has it as a internal function.
    require(f.selector != _governancePowerTransferByType(uint104,uint104,address,uint8).selector);

    uint256 bobVotingPowerBefore = getPowerCurrent(bob, VOTING_POWER());
    uint256 bobBalanceBefore = balanceOf(bob);
    address bobVotingDelegateBefore = getVotingDelegate(bob);

    // Require that Bob had voting power
    require(bobVotingPowerBefore > 0);

    env e;
    calldataarg args;
    address to;
    address from;
    uint256 amount;

    if (f.selector == transfer(address,uint256).selector){
        transfer(e,to,amount);
    } 

    uint256 bobVotingPowerAfter = getPowerCurrent(bob, VOTING_POWER());
    bool hasVotingPowerAfter = bobVotingPowerAfter > 0;

    assert !hasVotingPowerAfter;
}
*/

