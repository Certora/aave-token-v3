
/*
    This is a specification file for the verification of delegation
    features of AaveTokenV3.sol smart contract using the Certora prover. 
    For more information, visit: https://www.certora.com/

    This file is run with scripts/verifyDelegate.sh
    On AaveTokenV3Harness.sol

    Sanity check results: https://prover.certora.com/output/67509/021f59de6995d82ecf18/?anonymousKey=84f18dc61532a37fabfd59655fe7fe43989f1a8e

*/

import "base.spec";


/*
    @Rule

    @Description:
        If an account is not receiving delegation of power (one type) from anybody,
        and that account is not delegating that power to anybody, the power of that account
        must be equal to its token balance.

    @Note:

    @Link:
*/

rule powerWhenNotDelegating(address account) {
    mathint balance = balanceOf(account);
    bool isDelegatingVoting = getDelegatingVoting(account);
    bool isDelegatingProposition = getDelegatingProposition(account);
    uint72 dvb = getDelegatedVotingBalance(account);
    uint72 dpb = getDelegatedPropositionBalance(account);

    mathint votingPower = getPowerCurrent(account, VOTING_POWER());
    mathint propositionPower = getPowerCurrent(account, PROPOSITION_POWER());

    assert dvb == 0 && !isDelegatingVoting => votingPower == balance;
    assert dpb == 0 && !isDelegatingProposition => propositionPower == balance;
}


/**
    Account1 and account2 are not delegating power
*/

/*
    @Rule

    @Description:
        Verify correct voting power on token transfers, when both accounts are not delegating

    @Note:

    @Link:
*/

rule vpTransferWhenBothNotDelegating(address alice, address bob, address charlie, uint256 amount) {
    env e;
    require alice != bob && bob != charlie && alice != charlie;

    bool isAliceDelegatingVoting = getDelegatingVoting(alice);
    bool isBobDelegatingVoting = getDelegatingVoting(bob);

    // both accounts are not delegating
    require !isAliceDelegatingVoting && !isBobDelegatingVoting;

    mathint alicePowerBefore = getPowerCurrent(alice, VOTING_POWER());
    mathint bobPowerBefore = getPowerCurrent(bob, VOTING_POWER());
    mathint charliePowerBefore = getPowerCurrent(charlie, VOTING_POWER());

    transferFrom(e, alice, bob, amount);

    mathint alicePowerAfter = getPowerCurrent(alice, VOTING_POWER());
    mathint bobPowerAfter = getPowerCurrent(bob, VOTING_POWER());
    mathint charliePowerAfter = getPowerCurrent(charlie, VOTING_POWER());

    assert alicePowerAfter == alicePowerBefore - amount;
    assert bobPowerAfter == bobPowerBefore + amount;
    assert charliePowerAfter == charliePowerBefore;
}

 

rule vp_change_in_balance_affect_power_delegatee(method f, address alice) {
    env e;
    calldataarg args;

    bool isAliceDelegatingVoting = getDelegatingVoting(alice);

    address aliceD = getVotingDelegatee(alice); // aliceD == alice_delegatee
    require aliceD != alice && aliceD != 0;

    require (alice == 10 && aliceD==20);

    
    // both accounts are not delegating
    //require !isAliceDelegatingVoting;

    mathint alicePowerBefore = getPowerCurrent(alice, VOTING_POWER());
    //mathint bobPowerBefore = getPowerCurrent(bob, VOTING_POWER());
    //mathint charliePowerBefore = getPowerCurrent(charlie, VOTING_POWER());

    uint256 alice_bal_before = balanceOf(alice);
    mathint aliceD_bal_before = balanceOf(aliceD);
    mathint aliceD_power_before = getPowerCurrent(aliceD,VOTING_POWER());
    require (aliceD_power_before ==100);
    
    bool aliceD_is_delegating_before = getDelegatingVoting(aliceD);
    f(e,args);
    bool aliceD_is_delegating_after = getDelegatingVoting(aliceD);
    
    uint256 alice_bal_after = balanceOf(alice);
    mathint aliceD_bal_after = balanceOf(aliceD);
    mathint aliceD_power_after = getPowerCurrent(aliceD,VOTING_POWER());
    mathint the_increase = alice_bal_after-alice_bal_before;
    
    require (aliceD_bal_before == aliceD_bal_after);

    mathint alicePowerAfter = getPowerCurrent(alice, VOTING_POWER());

    assert aliceD_power_after == aliceD_power_before 
        - normalize(alice_bal_before) + normalize(alice_bal_after);
    
}



/*
    @Rule

    @Description:
        Verify correct proposition power on token transfers, when both accounts are not delegating

    @Note:

    @Link:
*/

rule ppTransferWhenBothNotDelegating(address alice, address bob, address charlie, uint256 amount) {
    env e;
    require alice != bob && bob != charlie && alice != charlie;

    bool isAliceDelegatingProposition = getDelegatingProposition(alice);
    bool isBobDelegatingProposition = getDelegatingProposition(bob);

    require !isAliceDelegatingProposition && !isBobDelegatingProposition;

    mathint alicePowerBefore = getPowerCurrent(alice, PROPOSITION_POWER());
    mathint bobPowerBefore = getPowerCurrent(bob, PROPOSITION_POWER());
    mathint charliePowerBefore = getPowerCurrent(charlie, PROPOSITION_POWER());

    transferFrom(e, alice, bob, amount);

    mathint alicePowerAfter = getPowerCurrent(alice, PROPOSITION_POWER());
    mathint bobPowerAfter = getPowerCurrent(bob, PROPOSITION_POWER());
    mathint charliePowerAfter = getPowerCurrent(charlie, PROPOSITION_POWER());

    assert alicePowerAfter == alicePowerBefore - amount;
    assert bobPowerAfter == bobPowerBefore + amount;
    assert charliePowerAfter == charliePowerBefore;
}

/*
    @Rule

    @Description:
        Verify correct voting power after Alice delegates to Bob, when 
        both accounts were not delegating

    @Note:

    @Link:
*/

rule vpDelegateWhenBothNotDelegating(address alice, address bob, address charlie) {
    env e;
    require alice == e.msg.sender;
    require alice != 0 && bob != 0 && charlie != 0;
    require alice != bob && bob != charlie && alice != charlie;

    bool isAliceDelegatingVoting = getDelegatingVoting(alice);
    bool isBobDelegatingVoting = getDelegatingVoting(bob);

    require !isAliceDelegatingVoting && !isBobDelegatingVoting;

    mathint aliceBalance = balanceOf(alice);
    mathint bobBalance = balanceOf(bob);

    mathint alicePowerBefore = getPowerCurrent(alice, VOTING_POWER());
    mathint bobPowerBefore = getPowerCurrent(bob, VOTING_POWER());
    mathint charliePowerBefore = getPowerCurrent(charlie, VOTING_POWER());

    delegate(e, bob);

    mathint alicePowerAfter = getPowerCurrent(alice, VOTING_POWER());
    mathint bobPowerAfter = getPowerCurrent(bob, VOTING_POWER());
    mathint charliePowerAfter = getPowerCurrent(charlie, VOTING_POWER());

    assert alicePowerAfter == alicePowerBefore - aliceBalance;
    assert bobPowerAfter == bobPowerBefore + (aliceBalance / DELEGATED_POWER_DIVIDER()) * DELEGATED_POWER_DIVIDER();
    assert getVotingDelegatee(alice) == bob;
    assert charliePowerAfter == charliePowerBefore;
}

/*
    @Rule

    @Description:
        Verify correct proposition power after Alice delegates to Bob, when 
        both accounts were not delegating

    @Note:

    @Link:
*/

rule ppDelegateWhenBothNotDelegating(address alice, address bob, address charlie) {
    env e;
    require alice == e.msg.sender;
    require alice != 0 && bob != 0 && charlie != 0;
    require alice != bob && bob != charlie && alice != charlie;

    bool isAliceDelegatingProposition = getDelegatingProposition(alice);
    bool isBobDelegatingProposition = getDelegatingProposition(bob);

    require !isAliceDelegatingProposition && !isBobDelegatingProposition;

    mathint aliceBalance = balanceOf(alice);
    mathint bobBalance = balanceOf(bob);

    mathint alicePowerBefore = getPowerCurrent(alice, PROPOSITION_POWER());
    mathint bobPowerBefore = getPowerCurrent(bob, PROPOSITION_POWER());
    mathint charliePowerBefore = getPowerCurrent(charlie, PROPOSITION_POWER());

    delegate(e, bob);

    mathint alicePowerAfter = getPowerCurrent(alice, PROPOSITION_POWER());
    mathint bobPowerAfter = getPowerCurrent(bob, PROPOSITION_POWER());
    mathint charliePowerAfter = getPowerCurrent(charlie, PROPOSITION_POWER());

    assert alicePowerAfter == alicePowerBefore - aliceBalance;
    assert bobPowerAfter == bobPowerBefore + (aliceBalance / DELEGATED_POWER_DIVIDER()) * DELEGATED_POWER_DIVIDER();
    assert getPropositionDelegatee(alice) == bob;
    assert charliePowerAfter == charliePowerBefore;
}

/**
    Account1 is delegating power to delegatee1, account2 is not delegating power to anybody
*/

/*
    @Rule

    @Description:
        Verify correct voting power after a token transfer from Alice to Bob, when 
        Alice was delegating and Bob wasn't

    @Note:

    @Link:
*/

rule vpTransferWhenOnlyOneIsDelegating(address alice, address bob, address charlie, uint256 amount) {
    env e;
    require alice != bob && bob != charlie && alice != charlie;

    bool isAliceDelegatingVoting = getDelegatingVoting(alice);
    bool isBobDelegatingVoting = getDelegatingVoting(bob);
    address aliceDelegate = getVotingDelegatee(alice);
    require aliceDelegate != alice && aliceDelegate != 0 && aliceDelegate != bob && aliceDelegate != charlie;

    require isAliceDelegatingVoting && !isBobDelegatingVoting;

    mathint alicePowerBefore = getPowerCurrent(alice, VOTING_POWER());
    // no delegation of anyone to Alice
    require alicePowerBefore == 0;

    mathint bobPowerBefore = getPowerCurrent(bob, VOTING_POWER());
    mathint charliePowerBefore = getPowerCurrent(charlie, VOTING_POWER());
    mathint aliceDelegatePowerBefore = getPowerCurrent(aliceDelegate, VOTING_POWER());
    uint256 aliceBalanceBefore = balanceOf(alice);

    transferFrom(e, alice, bob, amount);

    mathint alicePowerAfter = getPowerCurrent(alice, VOTING_POWER());
    mathint bobPowerAfter = getPowerCurrent(bob, VOTING_POWER());
    mathint charliePowerAfter = getPowerCurrent(charlie, VOTING_POWER());
    mathint aliceDelegatePowerAfter = getPowerCurrent(aliceDelegate, VOTING_POWER());
    uint256 aliceBalanceAfter = balanceOf(alice);

    assert alicePowerBefore == alicePowerAfter;
    assert aliceDelegatePowerAfter == 
        aliceDelegatePowerBefore - normalize(aliceBalanceBefore) + normalize(aliceBalanceAfter);
    assert bobPowerAfter == bobPowerBefore + amount;
    assert charliePowerBefore == charliePowerAfter;
}

/*
    @Rule

    @Description:
        Verify correct proposition power after a token transfer from Alice to Bob, when 
        Alice was delegating and Bob wasn't

    @Note:

    @Link:
*/

rule ppTransferWhenOnlyOneIsDelegating(address alice, address bob, address charlie, uint256 amount) {
    env e;
    require alice != bob && bob != charlie && alice != charlie;

    bool isAliceDelegatingProposition = getDelegatingProposition(alice);
    bool isBobDelegatingProposition = getDelegatingProposition(bob);
    address aliceDelegate = getPropositionDelegatee(alice);
    require aliceDelegate != alice && aliceDelegate != 0 && aliceDelegate != bob && aliceDelegate != charlie;

    require isAliceDelegatingProposition && !isBobDelegatingProposition;

    mathint alicePowerBefore = getPowerCurrent(alice, PROPOSITION_POWER());
    // no delegation of anyone to Alice
    require alicePowerBefore == 0;

    mathint bobPowerBefore = getPowerCurrent(bob, PROPOSITION_POWER());
    mathint charliePowerBefore = getPowerCurrent(charlie, PROPOSITION_POWER());
    mathint aliceDelegatePowerBefore = getPowerCurrent(aliceDelegate, PROPOSITION_POWER());
    uint256 aliceBalanceBefore = balanceOf(alice);

    transferFrom(e, alice, bob, amount);

    mathint alicePowerAfter = getPowerCurrent(alice, PROPOSITION_POWER());
    mathint bobPowerAfter = getPowerCurrent(bob, PROPOSITION_POWER());
    mathint charliePowerAfter = getPowerCurrent(charlie, PROPOSITION_POWER());
    mathint aliceDelegatePowerAfter = getPowerCurrent(aliceDelegate, PROPOSITION_POWER());
    uint256 aliceBalanceAfter = balanceOf(alice);

    // still zero
    assert alicePowerBefore == alicePowerAfter;
    assert aliceDelegatePowerAfter == 
        aliceDelegatePowerBefore - normalize(aliceBalanceBefore) + normalize(aliceBalanceAfter);
    assert bobPowerAfter == bobPowerBefore + amount;
    assert charliePowerBefore == charliePowerAfter;
}


/*
    @Rule

    @Description:
        Verify correct voting power after Alice stops delegating, when 
        Alice was delegating and Bob wasn't

    @Note:

    @Link:
*/
rule vpStopDelegatingWhenOnlyOneIsDelegating(address alice, address charlie) {
    env e;
    require alice != charlie;
    require alice == e.msg.sender;

    bool isAliceDelegatingVoting = getDelegatingVoting(alice);
    address aliceDelegate = getVotingDelegatee(alice);

    require isAliceDelegatingVoting && aliceDelegate != alice && aliceDelegate != 0 && aliceDelegate != charlie;

    mathint alicePowerBefore = getPowerCurrent(alice, VOTING_POWER());
    mathint charliePowerBefore = getPowerCurrent(charlie, VOTING_POWER());
    mathint aliceDelegatePowerBefore = getPowerCurrent(aliceDelegate, VOTING_POWER());

    delegate(e, 0);

    mathint alicePowerAfter = getPowerCurrent(alice, VOTING_POWER());
    mathint charliePowerAfter = getPowerCurrent(charlie, VOTING_POWER());
    mathint aliceDelegatePowerAfter = getPowerCurrent(aliceDelegate, VOTING_POWER());

    assert alicePowerAfter == alicePowerBefore + balanceOf(alice);
    assert aliceDelegatePowerAfter == aliceDelegatePowerBefore - normalize(balanceOf(alice));
    assert charliePowerAfter == charliePowerBefore;
}

/*
    @Rule

    @Description:
        Verify correct proposition power after Alice stops delegating, when 
        Alice was delegating and Bob wasn't

    @Note:

    @Link:
*/
rule ppStopDelegatingWhenOnlyOneIsDelegating(address alice, address charlie) {
    env e;
    require alice != charlie;
    require alice == e.msg.sender;

    bool isAliceDelegatingProposition = getDelegatingProposition(alice);
    address aliceDelegate = getPropositionDelegatee(alice);

    require isAliceDelegatingProposition && aliceDelegate != alice && aliceDelegate != 0 && aliceDelegate != charlie;

    mathint alicePowerBefore = getPowerCurrent(alice, PROPOSITION_POWER());
    mathint charliePowerBefore = getPowerCurrent(charlie, PROPOSITION_POWER());
    mathint aliceDelegatePowerBefore = getPowerCurrent(aliceDelegate, PROPOSITION_POWER());

    delegate(e, 0);

    mathint alicePowerAfter = getPowerCurrent(alice, PROPOSITION_POWER());
    mathint charliePowerAfter = getPowerCurrent(charlie, PROPOSITION_POWER());
    mathint aliceDelegatePowerAfter = getPowerCurrent(aliceDelegate, PROPOSITION_POWER());

    assert alicePowerAfter == alicePowerBefore + balanceOf(alice);
    assert aliceDelegatePowerAfter == aliceDelegatePowerBefore - normalize(balanceOf(alice));
    assert charliePowerAfter == charliePowerBefore;
}

/*
    @Rule

    @Description:
        Verify correct voting power after Alice delegates

    @Note:

    @Link:
*/
rule vpChangeDelegateWhenOnlyOneIsDelegating(address alice, address delegate2, address charlie) {
    env e;
    require alice != charlie && alice != delegate2 && charlie != delegate2;
    require alice == e.msg.sender;

    bool isAliceDelegatingVoting = getDelegatingVoting(alice);
    address aliceDelegate = getVotingDelegatee(alice);
    require aliceDelegate != alice && aliceDelegate != 0 && aliceDelegate != delegate2 && 
        delegate2 != 0 && delegate2 != charlie && aliceDelegate != charlie;

    require isAliceDelegatingVoting;

    mathint alicePowerBefore = getPowerCurrent(alice, VOTING_POWER());
    mathint charliePowerBefore = getPowerCurrent(charlie, VOTING_POWER());
    mathint aliceDelegatePowerBefore = getPowerCurrent(aliceDelegate, VOTING_POWER());
    mathint delegate2PowerBefore = getPowerCurrent(delegate2, VOTING_POWER());

    delegate(e, delegate2);

    mathint alicePowerAfter = getPowerCurrent(alice, VOTING_POWER());
    mathint charliePowerAfter = getPowerCurrent(charlie, VOTING_POWER());
    mathint aliceDelegatePowerAfter = getPowerCurrent(aliceDelegate, VOTING_POWER());
    mathint delegate2PowerAfter = getPowerCurrent(delegate2, VOTING_POWER());
    address aliceDelegateAfter = getVotingDelegatee(alice);

    assert alicePowerBefore == alicePowerAfter;
    assert aliceDelegatePowerAfter == aliceDelegatePowerBefore - normalize(balanceOf(alice));
    assert delegate2PowerAfter == delegate2PowerBefore + normalize(balanceOf(alice));
    assert aliceDelegateAfter == delegate2;
    assert charliePowerAfter == charliePowerBefore;
}

/*
    @Rule

    @Description:
        Verify correct proposition power after Alice delegates

    @Note:

    @Link:
*/
rule ppChangeDelegateWhenOnlyOneIsDelegating(address alice, address delegate2, address charlie) {
    env e;
    require alice != charlie && alice != delegate2 && charlie != delegate2;
    require alice == e.msg.sender;

    bool isAliceDelegatingVoting = getDelegatingProposition(alice);
    address aliceDelegate = getPropositionDelegatee(alice);
    require aliceDelegate != alice && aliceDelegate != 0 && aliceDelegate != delegate2 && 
        delegate2 != 0 && delegate2 != charlie && aliceDelegate != charlie;

    require isAliceDelegatingVoting;

    mathint alicePowerBefore = getPowerCurrent(alice, PROPOSITION_POWER());
    mathint charliePowerBefore = getPowerCurrent(charlie, PROPOSITION_POWER());
    mathint aliceDelegatePowerBefore = getPowerCurrent(aliceDelegate, PROPOSITION_POWER());
    mathint delegate2PowerBefore = getPowerCurrent(delegate2, PROPOSITION_POWER());

    delegate(e, delegate2);

    mathint alicePowerAfter = getPowerCurrent(alice, PROPOSITION_POWER());
    mathint charliePowerAfter = getPowerCurrent(charlie, PROPOSITION_POWER());
    mathint aliceDelegatePowerAfter = getPowerCurrent(aliceDelegate, PROPOSITION_POWER());
    mathint delegate2PowerAfter = getPowerCurrent(delegate2, PROPOSITION_POWER());
    address aliceDelegateAfter = getPropositionDelegatee(alice);

    assert alicePowerBefore == alicePowerAfter;
    assert aliceDelegatePowerAfter == aliceDelegatePowerBefore - normalize(balanceOf(alice));
    assert delegate2PowerAfter == delegate2PowerBefore + normalize(balanceOf(alice));
    assert aliceDelegateAfter == delegate2;
    assert charliePowerAfter == charliePowerBefore;
}

/*
    @Rule

    @Description:
        Verify correct voting power after Alice transfers to Bob, when only Bob was delegating

    @Note:

    @Link:
*/

rule vpOnlyAccount2IsDelegating(address alice, address bob, address charlie, uint256 amount) {
    env e;
    require alice != bob && bob != charlie && alice != charlie;

    bool isAliceDelegatingVoting = getDelegatingVoting(alice);
    bool isBobDelegatingVoting = getDelegatingVoting(bob);
    address bobDelegate = getVotingDelegatee(bob);
    require bobDelegate != bob && bobDelegate != 0 && bobDelegate != alice && bobDelegate != charlie;

    require !isAliceDelegatingVoting && isBobDelegatingVoting;

    mathint alicePowerBefore = getPowerCurrent(alice, VOTING_POWER());
    mathint bobPowerBefore = getPowerCurrent(bob, VOTING_POWER());
    require bobPowerBefore == 0;
    mathint charliePowerBefore = getPowerCurrent(charlie, VOTING_POWER());
    mathint bobDelegatePowerBefore = getPowerCurrent(bobDelegate, VOTING_POWER());
    uint256 bobBalanceBefore = balanceOf(bob);

    transferFrom(e, alice, bob, amount);

    mathint alicePowerAfter = getPowerCurrent(alice, VOTING_POWER());
    mathint bobPowerAfter = getPowerCurrent(bob, VOTING_POWER());
    mathint charliePowerAfter = getPowerCurrent(charlie, VOTING_POWER());
    mathint bobDelegatePowerAfter = getPowerCurrent(bobDelegate, VOTING_POWER());
    uint256 bobBalanceAfter = balanceOf(bob);

    assert alicePowerAfter == alicePowerBefore - amount;
    assert bobPowerAfter == 0;
    assert bobDelegatePowerAfter == bobDelegatePowerBefore - normalize(bobBalanceBefore) + normalize(bobBalanceAfter);

    assert charliePowerAfter == charliePowerBefore;
}

/*
    @Rule

    @Description:
        Verify correct proposition power after Alice transfers to Bob, when only Bob was delegating

    @Note:

    @Link:
*/

rule ppOnlyAccount2IsDelegating(address alice, address bob, address charlie, uint256 amount) {
    env e;
    require alice != bob && bob != charlie && alice != charlie;

    bool isAliceDelegating = getDelegatingProposition(alice);
    bool isBobDelegating = getDelegatingProposition(bob);
    address bobDelegate = getPropositionDelegatee(bob);
    require bobDelegate != bob && bobDelegate != 0 && bobDelegate != alice && bobDelegate != charlie;

    require !isAliceDelegating && isBobDelegating;

    mathint alicePowerBefore = getPowerCurrent(alice, PROPOSITION_POWER());
    mathint bobPowerBefore = getPowerCurrent(bob, PROPOSITION_POWER());
    require bobPowerBefore == 0;
    mathint charliePowerBefore = getPowerCurrent(charlie, PROPOSITION_POWER());
    mathint bobDelegatePowerBefore = getPowerCurrent(bobDelegate, PROPOSITION_POWER());
    uint256 bobBalanceBefore = balanceOf(bob);

    transferFrom(e, alice, bob, amount);

    mathint alicePowerAfter = getPowerCurrent(alice, PROPOSITION_POWER());
    mathint bobPowerAfter = getPowerCurrent(bob, PROPOSITION_POWER());
    mathint charliePowerAfter = getPowerCurrent(charlie, PROPOSITION_POWER());
    mathint bobDelegatePowerAfter = getPowerCurrent(bobDelegate, PROPOSITION_POWER());
    uint256 bobBalanceAfter = balanceOf(bob);

    assert alicePowerAfter == alicePowerBefore - amount;
    assert bobPowerAfter == 0;
    assert bobDelegatePowerAfter == bobDelegatePowerBefore - normalize(bobBalanceBefore) + normalize(bobBalanceAfter);

    assert charliePowerAfter == charliePowerBefore;
}


/*
    @Rule

    @Description:
        Verify correct voting power after Alice transfers to Bob, when both Alice
        and Bob were delegating

    @Note:

    @Link:
*/
rule vpTransferWhenBothAreDelegating(address alice, address bob, address charlie, uint256 amount) {
    env e;
    require alice != bob && bob != charlie && alice != charlie;

    bool isAliceDelegatingVoting = getDelegatingVoting(alice);
    bool isBobDelegatingVoting = getDelegatingVoting(bob);
    require isAliceDelegatingVoting && isBobDelegatingVoting;
    address aliceDelegate = getVotingDelegatee(alice);
    address bobDelegate = getVotingDelegatee(bob);
    require aliceDelegate != alice && aliceDelegate != 0 && aliceDelegate != bob && aliceDelegate != charlie;
    require bobDelegate != bob && bobDelegate != 0 && bobDelegate != alice && bobDelegate != charlie;
    require aliceDelegate != bobDelegate;

    mathint alicePowerBefore = getPowerCurrent(alice, VOTING_POWER());
    mathint bobPowerBefore = getPowerCurrent(bob, VOTING_POWER());
    mathint charliePowerBefore = getPowerCurrent(charlie, VOTING_POWER());
    mathint aliceDelegatePowerBefore = getPowerCurrent(aliceDelegate, VOTING_POWER());
    mathint bobDelegatePowerBefore = getPowerCurrent(bobDelegate, VOTING_POWER());
    uint256 aliceBalanceBefore = balanceOf(alice);
    uint256 bobBalanceBefore = balanceOf(bob);

    transferFrom(e, alice, bob, amount);

    mathint alicePowerAfter = getPowerCurrent(alice, VOTING_POWER());
    mathint bobPowerAfter = getPowerCurrent(bob, VOTING_POWER());
    mathint charliePowerAfter = getPowerCurrent(charlie, VOTING_POWER());
    mathint aliceDelegatePowerAfter = getPowerCurrent(aliceDelegate, VOTING_POWER());
    mathint bobDelegatePowerAfter = getPowerCurrent(bobDelegate, VOTING_POWER());
    uint256 aliceBalanceAfter = balanceOf(alice);
    uint256 bobBalanceAfter = balanceOf(bob);

    assert alicePowerAfter == alicePowerBefore;
    assert bobPowerAfter == bobPowerBefore;
    assert aliceDelegatePowerAfter == aliceDelegatePowerBefore - normalize(aliceBalanceBefore) 
        + normalize(aliceBalanceAfter);

    mathint normalizedBalanceBefore = normalize(bobBalanceBefore);
    mathint normalizedBalanceAfter = normalize(bobBalanceAfter);
    assert bobDelegatePowerAfter == bobDelegatePowerBefore - normalizedBalanceBefore + normalizedBalanceAfter;
}

/*
    @Rule

    @Description:
        Verify correct proposition power after Alice transfers to Bob, when both Alice
        and Bob were delegating

    @Note:

    @Link:
*/
rule ppTransferWhenBothAreDelegating(address alice, address bob, address charlie, uint256 amount) {
    env e;
    require alice != bob && bob != charlie && alice != charlie;

    bool isAliceDelegating = getDelegatingProposition(alice);
    bool isBobDelegating = getDelegatingProposition(bob);
    require isAliceDelegating && isBobDelegating;
    address aliceDelegate = getPropositionDelegatee(alice);
    address bobDelegate = getPropositionDelegatee(bob);
    require aliceDelegate != alice && aliceDelegate != 0 && aliceDelegate != bob && aliceDelegate != charlie;
    require bobDelegate != bob && bobDelegate != 0 && bobDelegate != alice && bobDelegate != charlie;
    require aliceDelegate != bobDelegate;

    mathint alicePowerBefore = getPowerCurrent(alice, PROPOSITION_POWER());
    mathint bobPowerBefore = getPowerCurrent(bob, PROPOSITION_POWER());
    mathint charliePowerBefore = getPowerCurrent(charlie, PROPOSITION_POWER());
    mathint aliceDelegatePowerBefore = getPowerCurrent(aliceDelegate, PROPOSITION_POWER());
    mathint bobDelegatePowerBefore = getPowerCurrent(bobDelegate, PROPOSITION_POWER());
    uint256 aliceBalanceBefore = balanceOf(alice);
    uint256 bobBalanceBefore = balanceOf(bob);

    transferFrom(e, alice, bob, amount);

    mathint alicePowerAfter = getPowerCurrent(alice, PROPOSITION_POWER());
    mathint bobPowerAfter = getPowerCurrent(bob, PROPOSITION_POWER());
    mathint charliePowerAfter = getPowerCurrent(charlie, PROPOSITION_POWER());
    mathint aliceDelegatePowerAfter = getPowerCurrent(aliceDelegate, PROPOSITION_POWER());
    mathint bobDelegatePowerAfter = getPowerCurrent(bobDelegate, PROPOSITION_POWER());
    uint256 aliceBalanceAfter = balanceOf(alice);
    uint256 bobBalanceAfter = balanceOf(bob);

    assert alicePowerAfter == alicePowerBefore;
    assert bobPowerAfter == bobPowerBefore;
    assert aliceDelegatePowerAfter == aliceDelegatePowerBefore - normalize(aliceBalanceBefore) 
        + normalize(aliceBalanceAfter);

    mathint normalizedBalanceBefore = normalize(bobBalanceBefore);
    mathint normalizedBalanceAfter = normalize(bobBalanceAfter);
    assert bobDelegatePowerAfter == bobDelegatePowerBefore - normalizedBalanceBefore + normalizedBalanceAfter;
}

/*
    @Rule

    @Description:
        Verify that an account's delegate changes only as a result of a call to
        the delegation functions

    @Note:

    @Link:
*/
rule votingDelegateChanges(address alice, method f) {
    env e;
    calldataarg args;

    address aliceVotingDelegateBefore = getVotingDelegatee(alice);
    address alicePropDelegateBefore = getPropositionDelegatee(alice);

    f(e, args);

    address aliceVotingDelegateAfter = getVotingDelegatee(alice);
    address alicePropDelegateAfter = getPropositionDelegatee(alice);

    // only these four function may change the delegate of an address
    assert aliceVotingDelegateAfter != aliceVotingDelegateBefore || alicePropDelegateBefore != alicePropDelegateAfter =>
        f.selector == sig:delegate(address).selector || 
        f.selector == sig:delegateByType(address,IGovernancePowerDelegationToken.GovernancePowerType).selector ||
        f.selector == sig:metaDelegate(address,address,uint256,uint8,bytes32,bytes32).selector ||
        f.selector == sig:metaDelegateByType(address,address,IGovernancePowerDelegationToken.GovernancePowerType,uint256,uint8,bytes32,bytes32).selector;
}

/*
    @Rule

    @Description:
        Verify that an account's voting and proposition power changes only as a result of a call to
        the delegation and transfer functions

    @Note:

    @Link:
*/
rule votingPowerChanges(address alice, method f) {
    env e;
    calldataarg args;

    uint aliceVotingPowerBefore = getPowerCurrent(alice, VOTING_POWER());
    uint alicePropPowerBefore = getPowerCurrent(alice, PROPOSITION_POWER());

    f(e, args);

    uint aliceVotingPowerAfter = getPowerCurrent(alice, VOTING_POWER());
    uint alicePropPowerAfter = getPowerCurrent(alice, PROPOSITION_POWER());

    // only these four function may change the power of an address
    assert aliceVotingPowerAfter != aliceVotingPowerBefore || alicePropPowerAfter != alicePropPowerBefore =>
        f.selector == sig:delegate(address).selector || 
        f.selector == sig:delegateByType(address,IGovernancePowerDelegationToken.GovernancePowerType).selector ||
        f.selector == sig:metaDelegate(address,address,uint256,uint8,bytes32,bytes32).selector ||
        f.selector == sig:metaDelegateByType(address,address,IGovernancePowerDelegationToken.GovernancePowerType,uint256,uint8,bytes32,bytes32).selector ||
        f.selector == sig:transfer(address,uint256).selector ||
        f.selector == sig:transferFrom(address,address,uint256).selector;
}    

/*
    @Rule

    @Description:
        Verify that only delegate() and metaDelegate() may change both voting and
        proposition delegates of an account at once.
        nissan: I added also delegateByType() here.

    @Note:

    @Link:
*/
rule delegationTypeIndependence(address who, method f) filtered { f -> !f.isView } {
    address _delegateeV = getVotingDelegatee(who);
    address _delegateeP = getPropositionDelegatee(who);
	
    env e;
    calldataarg arg;
    f(e, arg);
	
    address delegateeV_ = getVotingDelegatee(who);
    address delegateeP_ = getPropositionDelegatee(who);
    assert _delegateeV != delegateeV_ && _delegateeP != delegateeP_ =>
        (f.selector == sig:delegate(address).selector ||
         f.selector == sig:metaDelegate(address,address,uint256,uint8,bytes32,bytes32).selector ||
         f.selector == sig:delegateByType(address,
                                  IGovernancePowerDelegationToken.GovernancePowerType).selector ||
         f.selector == sig:metaDelegateByType(address,address,
                                              IGovernancePowerDelegationToken.GovernancePowerType,
                                              uint256,uint8,bytes32,bytes32).selector
        ),
        "one delegatee type stays the same, unless delegate or delegateBySig was called";
}

/*
    @Rule

    @Description:
        Verifies that delegating twice to the same delegate changes the delegate's
        voting power only once.

    @Note:

    @Link:
*/
rule cantDelegateTwice(address _delegate) {
    env e;

    address delegateBeforeV = getVotingDelegatee(e.msg.sender);
    address delegateBeforeP = getPropositionDelegatee(e.msg.sender);
    require delegateBeforeV != _delegate && delegateBeforeV != e.msg.sender && delegateBeforeV != 0;
    require delegateBeforeP != _delegate && delegateBeforeP != e.msg.sender && delegateBeforeP != 0;
    require _delegate != e.msg.sender && _delegate != 0 && e.msg.sender != 0;
    require getDelegationMode(e.msg.sender) == FULL_POWER_DELEGATED();

    mathint votingPowerBefore = getPowerCurrent(_delegate, VOTING_POWER());
    mathint propPowerBefore = getPowerCurrent(_delegate, PROPOSITION_POWER());
    
    delegate(e, _delegate);
    
    mathint votingPowerAfter = getPowerCurrent(_delegate, VOTING_POWER());
    mathint propPowerAfter = getPowerCurrent(_delegate, PROPOSITION_POWER());

    delegate(e, _delegate);

    mathint votingPowerAfter2 = getPowerCurrent(_delegate, VOTING_POWER());
    mathint propPowerAfter2 = getPowerCurrent(_delegate, PROPOSITION_POWER());

    assert votingPowerAfter == votingPowerBefore + normalize(balanceOf(e.msg.sender));
    assert propPowerAfter == propPowerBefore + normalize(balanceOf(e.msg.sender));
    assert votingPowerAfter2 == votingPowerAfter && propPowerAfter2 == propPowerAfter;
}

/*
    @Rule

    @Description:
        transfer and transferFrom change voting/proposition power identically

    @Note:

    @Link:
*/
rule transferAndTransferFromPowerEquivalence(address bob, uint amount) {
    env e1;
    env e2;
    storage init = lastStorage;

    address alice;
    require alice == e1.msg.sender;

    uint aliceVotingPowerBefore = getPowerCurrent(alice, VOTING_POWER());
    uint alicePropPowerBefore = getPowerCurrent(alice, PROPOSITION_POWER());

    transfer(e1, bob, amount);

    uint aliceVotingPowerAfterTransfer = getPowerCurrent(alice, VOTING_POWER());
    uint alicePropPowerAfterTransfer = getPowerCurrent(alice, PROPOSITION_POWER());

    transferFrom(e2, alice, bob, amount) at init;

    uint aliceVotingPowerAfterTransferFrom = getPowerCurrent(alice, VOTING_POWER());
    uint alicePropPowerAfterTransferFrom = getPowerCurrent(alice, PROPOSITION_POWER());

    assert aliceVotingPowerAfterTransfer == aliceVotingPowerAfterTransferFrom &&
           alicePropPowerAfterTransfer == alicePropPowerAfterTransferFrom;

}





rule simple_rule(address alice1, address alice2, address bob, address charlie,
                 uint256 amount, uint256 amount2) {
    require (alice1 != bob && alice1 != charlie && bob != charlie);
    require (alice2 != bob && alice2 != charlie && alice2 != alice1);
    require (alice1 !=0 && bob != 0 && charlie != 0 && alice2 != 0);
    
    bool is_alice1_delegating_voting = getDelegatingVoting(alice1);
    bool is_alice2_delegating_voting = getDelegatingVoting(alice2);
    bool is_bob_delegating_voting = getDelegatingVoting(bob);
    bool is_charlie_delegating_voting = getDelegatingVoting(charlie);
    address alice1_delegatee = getVotingDelegatee(alice1);
    address alice2_delegatee = getVotingDelegatee(alice2);
    require is_alice1_delegating_voting && is_alice2_delegating_voting &&
        !is_bob_delegating_voting && !is_charlie_delegating_voting;
    require alice1_delegatee == bob;
    require alice2_delegatee == bob;
    
    uint256 alice1_balance_before = balanceOf(alice1);
    uint256 alice2_balance_before = balanceOf(alice2);
    uint256 bob_balance_before = balanceOf(bob);
    uint256 alice1_power_before = getPowerCurrent(alice1, VOTING_POWER());
    uint256 alice2_power_before = getPowerCurrent(alice2, VOTING_POWER());
    mathint bob_power_before = getPowerCurrent(bob, VOTING_POWER());

    //require alice1_balance_before == 0;
    //require alice2_balance_before == 0;
    //require alice1_power_before == 0;
    //require alice2_power_before == 0;
    
    //require bob_balance_before == 0;
    //require bob_power_before == 1000;
    //require amount2 == 0;
    //require amount == 10000000000;

    require (bob_power_before ==
             normalize(alice1_balance_before)+normalize(alice2_balance_before) + bob_balance_before
            );
        
    env e;
    transferFrom(e, charlie, alice1, amount);
    transferFrom(e, charlie, alice2, amount2);

    uint256 alice1_balance_after = balanceOf(alice1);
    uint256 alice2_balance_after = balanceOf(alice2);
    uint256 bob_balance_after = balanceOf(bob);
    mathint bob_power_after = getPowerCurrent(bob, VOTING_POWER());

    assert (bob_power_after ==
            normalize(alice1_balance_after)+normalize(alice2_balance_after) + bob_balance_after
           );
    assert (bob_power_after ==
            bob_power_before +
            normalize(alice1_balance_after) - normalize(alice1_balance_before) +
            normalize(alice2_balance_after) - normalize(alice2_balance_before)
           );
}



/* The following invariant says that the voting power of a user is as it should be.
   That is, the sum of all balances of users that delegate to him, plus his balance in case 
   that he is not delegating  */

// From VAULT spec
/*
invariant inv_sumAllBalance_eq_totalSupply()
    sumAllBalance() == to_mathint(totalSupply())
    filtered {f -> f.selector != sig:havoc_all().selector}
ghost sumAllBalance() returns mathint {
    init_state axiom sumAllBalance() == 0;
}
hook Sstore _balances[KEY address a] uint256 balance (uint256 old_balance) STORAGE {
  havoc sumAllBalance assuming sumAllBalance@new() == sumAllBalance@old() + balance - old_balance;
}
hook Sload uint256 balance _balances[KEY address a] STORAGE {
    require to_mathint(balance) <= sumAllBalance();
}
*/

/*
ghost mapping(address => bool) mirror_approvedSenders { 
    init_state axiom forall address a. mirror_approvedSenders[a] == false;
}
hook Sstore _approvedSenders[KEY address key] bool newVal (bool oldVal) STORAGE {
    mirror_approvedSenders[key] = newVal;
}
hook Sload bool val _approvedSenders[KEY address key] STORAGE {
    require(mirror_approvedSenders[key] == val);
}
*/

ghost mapping(address => mathint) sum_all_delegated_power {
    init_state axiom forall address delegatee. sum_all_delegated_power[delegatee] == 0;
}


ghost mapping(address => AaveTokenV3Harness.DelegationMode) mirror_delegationMode { 
    init_state axiom forall address a. mirror_delegationMode[a] == AaveTokenV3Harness.DelegationMode.NO_DELEGATION;
}
hook Sstore _balances[KEY address a].delegationMode AaveTokenV3Harness.DelegationMode newVal (AaveTokenV3Harness.DelegationMode oldVal) STORAGE {
    mirror_delegationMode[a] = newVal;

    if ( (newVal==VOTING_DELEGATED() || newVal==FULL_POWER_DELEGATED())
         &&
         (oldVal!=VOTING_DELEGATED() && oldVal!=FULL_POWER_DELEGATED())
       ) { // if we start to delegate now
        sum_all_delegated_power[mirror_votingDelegatee[a]] =
            sum_all_delegated_power[mirror_votingDelegatee[a]] +
            (mirror_balance[a]/(10^10)*(10^10));
    }
}
hook Sload AaveTokenV3Harness.DelegationMode val _balances[KEY address a].delegationMode STORAGE {
    require(mirror_delegationMode[a] == val);
}
invariant mirror_delegationMode_correct()
    forall address a.mirror_delegationMode[a] == getDelegationMode(a);


ghost mapping(address => address) mirror_votingDelegatee { 
    init_state axiom forall address a. mirror_votingDelegatee[a] == 0;
}
hook Sstore _votingDelegatee[KEY address delegator] address new_delegatee (address old_delegatee) STORAGE {
    mirror_votingDelegatee[delegator] = new_delegatee;
    if ((mirror_delegationMode[delegator]==FULL_POWER_DELEGATED() ||
         mirror_delegationMode[delegator]==VOTING_DELEGATED()) &&
        new_delegatee != old_delegatee) { // if a delegator changes his delegatee
        sum_all_delegated_power[new_delegatee] =
            sum_all_delegated_power[new_delegatee] + (mirror_balance[delegator]/(10^10)*(10^10));
        sum_all_delegated_power[old_delegatee] = 
            sum_all_delegated_power[old_delegatee] - (mirror_balance[delegator]/(10^10)*(10^10));
    }
}
hook Sload address val _votingDelegatee[KEY address delegator] STORAGE {
    require(mirror_votingDelegatee[delegator] == val);
}
invariant mirror_votingDelegatee_correct()
    forall address a.mirror_votingDelegatee[a] == getVotingDelegatee(a);



ghost mapping(address => uint104) mirror_balance { 
    init_state axiom forall address a. mirror_balance[a] == 0;
}
hook Sstore _balances[KEY address a].balance uint104 balance (uint104 old_balance) STORAGE {
    mirror_balance[a] = balance;
    //sum_all_delegated_power[a] = sum_all_delegated_power[a] + balance - old_balance;
    // The code should be:
    // if a delegates to b, sum_all_delegated_power[b] += the diff of balances of a
    if (a!=0 &&
        (mirror_delegationMode[a]==FULL_POWER_DELEGATED() ||
         mirror_delegationMode[a]==VOTING_DELEGATED() )
        )
        sum_all_delegated_power[mirror_votingDelegatee[a]] = sum_all_delegated_power[mirror_votingDelegatee[a]] + (balance/ (10^10) * (10^10)) - (old_balance/ (10^10) * (10^10)) ;
}
hook Sload uint104 bal _balances[KEY address a].balance STORAGE {
    require(mirror_balance[a] == bal);
    // nissan: need to remove the following line
    require to_mathint(bal) <= sum_all_delegated_power[a];
    // The code should be (under require):
    // if a delegates to b, bal <= sum_all_delegated_power[b]
}
invariant mirror_balance_correct()
    forall address a.mirror_balance[a] == getBalance(a);


invariant inv_voting_power_correct(address user) 
    user != 0 =>
    (
     to_mathint(getPowerCurrent(user, VOTING_POWER()))
     ==
     sum_all_delegated_power[user] +
     ( (mirror_delegationMode[user]==FULL_POWER_DELEGATED() ||
        mirror_delegationMode[user]==VOTING_DELEGATED())     ? 0 : mirror_balance[user])
    )
    filtered { f -> 
    f.selector != sig:delegateByType(address,IGovernancePowerDelegationToken.GovernancePowerType).selector &&
    f.selector != sig:metaDelegateByType(address,address,IGovernancePowerDelegationToken.GovernancePowerType,uint256,uint8,bytes32,bytes32).selector
}
{
    preserved with (env e) {
        requireInvariant user_cant_delegate_to_himself();
    }
}





rule voting_power_correct(method f,
                          address alice, address bob, address charlie, uint256 amount)
    filtered { f -> 
        f.selector != sig:delegateByType(address,IGovernancePowerDelegationToken.GovernancePowerType).selector &&
        f.selector != sig:metaDelegateByType(address,address,IGovernancePowerDelegationToken.GovernancePowerType,uint256,uint8,bytes32,bytes32).selector
        }

{
    env e;
    calldataarg args;

    requireInvariant user_cant_delegate_to_himself();
    require (bob != 0);

    require (bob==10);
    require (alice ==10);
    require (e.msg.sender == 2);
    
    bool is_bob_delegating_voting_before = getDelegatingVoting(bob);
    mathint bob_power_before = getPowerCurrent(bob, VOTING_POWER());
    uint256 bob_balance_before = balanceOf(bob);
    uint256 alice_balance_before = balanceOf(alice);
    require alice_balance_before == 10^10;

    address bob_delegatee_before = getVotingDelegatee(bob);
    
    require
        bob_power_before == sum_all_delegated_power[bob] +
        ( (mirror_delegationMode[bob]==FULL_POWER_DELEGATED() ||
           mirror_delegationMode[bob]==VOTING_DELEGATED())     ? 0 : mirror_balance[bob]);

    
    f(e, args);
    //    transferFrom(e, charlie, alice, amount);
    //IGovernancePowerDelegationToken.GovernancePowerType type;
    //    type = IGovernancePowerDelegationToken.GovernancePowerType.VOTING;
    //delegateByType(e,alice,type);

    bool is_bob_delegating_voting_after = getDelegatingVoting(bob);
    uint256 bob_balance_after = balanceOf(bob);
    mathint bob_power_after = getPowerCurrent(bob, VOTING_POWER());

    assert
        bob_power_after == sum_all_delegated_power[bob] +
        ( (mirror_delegationMode[bob]==FULL_POWER_DELEGATED() ||
           mirror_delegationMode[bob]==VOTING_DELEGATED())     ? 0 : mirror_balance[bob]);
}



rule delegated_voting_power_correct(method f, address alice, address bob)
//    filtered { f -> 
//      f.selector != sig:delegateByType(address,IGovernancePowerDelegationToken.GovernancePowerType).selector &&
//      f.selector != sig:metaDelegateByType(address,address,IGovernancePowerDelegationToken.GovernancePowerType,uint256,uint8,bytes32,bytes32).selector
//      }
{
    env e;
    calldataarg args;

    requireInvariant user_cant_delegate_to_himself();
    require (bob != 0);
    
    bool is_bob_delegating_voting_before = getDelegatingVoting(bob);
    uint256 bob_balance_before = balanceOf(bob);
    uint256 alice_balance_before = balanceOf(alice);
    address bob_delegatee_before = getVotingDelegatee(bob);
    
    mathint bob_power_before = getDelegatedPowerVoting(e,bob);
    require bob_power_before == sum_all_delegated_power[bob];
    
    f(e, args);
    //    transferFrom(e, charlie, alice, amount);
    //IGovernancePowerDelegationToken.GovernancePowerType type;
    //    type = IGovernancePowerDelegationToken.GovernancePowerType.VOTING;
    //delegateByType(e,alice,type);

    bool is_bob_delegating_voting_after = getDelegatingVoting(bob);
    uint256 bob_balance_after = balanceOf(bob);

    mathint bob_power_after = getDelegatedPowerVoting(e,bob);
    assert  bob_power_after == sum_all_delegated_power[bob];
}


rule what_can_change_in_a_single_call(method f, address bob) {
    env e;
    calldataarg args;

    require (bob != 0);

    uint256 bob_balance_before = balanceOf(bob);
    bool is_bob_delegating_voting_before = getDelegatingVoting(bob);
    address bob_delegatee_before = mirror_votingDelegatee[bob];

    f(e,args);

    uint256 bob_balance_after = balanceOf(bob);
    bool is_bob_delegating_voting_after = getDelegatingVoting(bob);
    address bob_delegatee_after = mirror_votingDelegatee[bob];

    assert (bob_balance_before != bob_balance_after =>
            (is_bob_delegating_voting_before==is_bob_delegating_voting_after &&
             bob_delegatee_before == bob_delegatee_after)
           );

    assert (bob_delegatee_before != bob_delegatee_after =>
            bob_balance_before == bob_balance_after
           );

    assert (is_bob_delegating_voting_before!=is_bob_delegating_voting_after =>
            bob_balance_before == bob_balance_after            
            );
  
}



rule r_user_cant_delegate_to_himself(method f, address bob) {
    env e;
    calldataarg args;
    require (bob != 0);

    uint256 bob_balance_before = balanceOf(bob);
    bool is_bob_delegating_voting_before = getDelegatingVoting(bob);
    address bob_delegatee_before = mirror_votingDelegatee[bob];

    require (mirror_votingDelegatee[bob]!=bob);
    
    f(e,args);

    uint256 bob_balance_after = balanceOf(bob);
    bool is_bob_delegating_voting_after = getDelegatingVoting(bob);
    address bob_delegatee_after = mirror_votingDelegatee[bob];

    assert (mirror_votingDelegatee[bob]!=bob);
    
}

invariant user_cant_delegate_to_himself()
    forall address a. a!=0 => mirror_votingDelegatee[a] != a;
