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
    getdelegationStatus(address user) returns (uint8) envfree
    getNonce(address user) returns (uint256) envfree
    getPowerCurrent(address user) returns (uint256) envfree
}

// CONSTANTS :- GovernancyType enum from the token contract
definition VOTING_POWER() returns uint8 = 0;
definition PROPOSITION_POWER() returns uint8 = 1;

definition DELEGATED_POWER_DIVIDER() returns uint256 = 10^10;

// 16000000 * 10^18 is the maximum supply of the AAVE token
definition MAX_DELEGATED_BALANCE() returns uint256 = 16000000 * 10^18 / DELEGATED_POWER_DIVIDER();

function normalize(uint256 amount) returns uint256 {
    return to_uint256(amount / DELEGATED_POWER_DIVIDER() * DELEGATED_POWER_DIVIDER());
}

rule methodsVacuityCheck(method f,calldataarg args,env e){
    f(e,args);
    assert false;
}

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

/* Verify that only delegate functions can change someone's delegate. */

rule votingDelegateChanges(address alice, method f) filtered {f -> !f.isFallback }{
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


ghost mathint sumBalances {
    init_state axiom sumBalances == 0;
}

hook Sstore _balances[KEY address user].balance uint104 balance
    (uint104 old_balance) STORAGE {
        sumBalances = sumBalances - to_mathint(old_balance) + to_mathint(balance);
    }
    
invariant totalSupplyEqualsBalances()
    sumBalances == totalSupply()


// MY spec


/* 1.If voting power of user is not (user balance + delegatedVotingBalance * 10^10) the it must mean he has delegated his voting power , similarly for propostion power. */

rule ifPowerNotMaxThanPowerMustBeDelegated{
    address b;
    require(b!=0);
    assert getPowerCurrent(b,VOTING_POWER()) < to_uint256(getBalance(b)+to_uint256(getDelegatedVotingBalance(b))) => getDelegatingVoting(b),"if current voting power is less than maximum than the person must have delegated his voting power";
    assert getPowerCurrent(b,PROPOSITION_POWER()) < to_uint256(getBalance(b)+to_uint256(getDelegatedPropositionBalance(b))) => getDelegatingProposition(b),"if current proposition power is less than maximum than the person must have delegated his propistion power";
}

/* 2.Power and balance of zero address must be zero */

rule zeroAddressCheck(env e,method f,calldataarg args) filtered {f -> !f.isFallback }{
    address zero=0;
    require(getBalance(zero)==0 && getdelegationStatus(zero)==0 && getDelegatedVotingBalance(zero)==0 && getDelegatedPropositionBalance(zero)==0 && getBalance(0)==0);
    require(e.msg.sender!=0);
    f(e,args);
    assert getBalance(zero)==0 && getdelegationStatus(zero)==0 && getDelegatedVotingBalance(zero)==0 && getDelegatedPropositionBalance(zero)==0 && getBalance(0)==0,"Power of zero address cannot be changed";
}

/* 3.If user delegatioin status is non-zero than he must have non-zero voting delegatee or proposition delegatee.*/

rule correctnessOfDelegationState(address user,method f,env e,calldataarg args) filtered {f -> !f.isFallback }{

    require(user!=0 && getdelegationStatus(user)==0 && getVotingDelegate(user) == 0 && getPropositionDelegate(user)==0);
    f(e,args);
    assert getdelegationStatus(user)!=0 <=> (getVotingDelegate(user) != 0 &&  getVotingDelegate(user) != user) ||  (getPropositionDelegate(user)!=0 && getPropositionDelegate(user)!=user);

}

/* 4.One delegation power type must not affect the other power type.*/

rule integrityOfDelegateByType(address bob,env e ,method f,calldataarg args){
    address alice=e.msg.sender;
    require(alice!=0);

    uint256 bobPropositionPowerBefore=getPowerCurrent(bob,PROPOSITION_POWER());
    delegateByType(e,bob,VOTING_POWER());
    uint256 bobPropositionPowerAfter=getPowerCurrent(bob,PROPOSITION_POWER());
    uint256 bobVotingPowerBefore=getPowerCurrent(bob,VOTING_POWER());
    delegateByType(e,bob,PROPOSITION_POWER());
    uint256 bobVotingPowerAfter=getPowerCurrent(bob,VOTING_POWER());


    assert bobPropositionPowerBefore==bobPropositionPowerAfter,"Delegating voting power must not change proposition power of delegatee";
    assert bobVotingPowerBefore==bobVotingPowerAfter,"Delegating propostion power must not change voting power of delegatee";
}

/* 5.After transfer between A & B , the delegatedVoting/delegatedPropositionBalance of A or B must not change unless one of them is delegatee of other. */

rule inTransferDelegatedBalanceOnlyChangesIfEitherOfTwoIsDelegateeOfOther(env e1){
    address alice=e1.msg.sender;
    address bob;
    uint256 amount;
    address aliceVotingDelegatee=getVotingDelegate(alice);
    address alicePropositionDelegatee=getPropositionDelegate(alice);
    address bobVotingDelegatee=getVotingDelegate(bob);
    address bobPropositionDelegatee=getPropositionDelegate(bob);

    uint72 aliceDelegatedVotingBalanceBefore=getDelegatedVotingBalance(alice);
    uint72 bobDelegatedVotingBalanceBefore=getDelegatedVotingBalance(bob);
    uint72 aliceDelegatedPropositionBalanceBefore=getDelegatedPropositionBalance(alice);
    uint72 bobDelegatedPropositionBalanceBefore=getDelegatedPropositionBalance(bob);


    require(aliceVotingDelegatee!=alice && alicePropositionDelegatee!=alice && bobVotingDelegatee!=bob && bobPropositionDelegatee!=bob);

    transfer(e1,bob,amount);

    uint72 aliceDelegatedVotingBalanceAfter=getDelegatedVotingBalance(alice);
    uint72 bobDelegatedVotingBalanceAfter=getDelegatedVotingBalance(bob);
    uint72 aliceDelegatedPropositionBalanceAfter=getDelegatedPropositionBalance(alice);
    uint72 bobDelegatedPropositionBalanceAfter=getDelegatedPropositionBalance(bob);

    assert aliceDelegatedVotingBalanceBefore != aliceDelegatedVotingBalanceAfter => bobVotingDelegatee==alice,"Transfer must not affect delegated balance unless one of the partcipant is delegatee of the other";
    assert bobDelegatedVotingBalanceBefore!=bobDelegatedVotingBalanceAfter => aliceVotingDelegatee==bob,"Transfer must not affect delegated balance unless one of the partcipant is delegatee of the other";
    assert aliceDelegatedPropositionBalanceBefore != aliceDelegatedPropositionBalanceAfter => bobPropositionDelegatee==alice,"Transfer must not affect delegated balance unless one of the partcipant is delegatee of the other";
    assert bobDelegatedPropositionBalanceBefore!=bobDelegatedPropositionBalanceAfter => alicePropositionDelegatee==bob,"Transfer must not affect delegated balance unless one of the partcipant is delegatee of the other";
}
 

/* 6.voting power can only increase if
        1.Balance increases.
        2.delegated voting balance increases.
        3.undelegate voting power if already delegated.
*/

rule votingPowerCanOnlyIncreaseInCertainConditions(address alice,method f,env e,calldataarg args) filtered {f -> !f.isFallback }{
    uint256 aliceVotingPowerBefore=getPowerCurrent(alice,VOTING_POWER());
    uint8 aliceDelegationStatusBefore=getdelegationStatus(alice);
    uint104 aliceBalanceBefore=getBalance(alice);
    uint72 aliceDelegatedVotingBalanceBefore=getDelegatedVotingBalance(alice);

    f(e,args);

    uint256 aliceVotingPowerAfter=getPowerCurrent(alice,VOTING_POWER());
    uint8 aliceDelegationStatusAfter=getdelegationStatus(alice);
    uint104 aliceBalanceAfter=getBalance(alice);
    uint72 aliceDelegatedVotingBalanceAfter=getDelegatedVotingBalance(alice);

    assert aliceVotingPowerAfter>aliceVotingPowerBefore => (aliceBalanceAfter>aliceBalanceBefore || aliceDelegatedVotingBalanceAfter>aliceDelegatedVotingBalanceBefore || ((aliceDelegationStatusAfter ==0 || aliceDelegationStatusAfter==2) && (aliceDelegationStatusBefore==1 || aliceDelegationStatusBefore==3))) , "voting power can only increase if 1.Balance increases. 2. delegated voting balance increases. 3. undelegate voting power if already delegated.";
}

/* 7.proposition power can only increase if
        1.Balance increases.
        2.delegated voting balance increases.
        3.undelegate proposition power if already delegated.
*/

rule propositionPowerCanOnlyIncreaseInCertainConditions(address alice,method f,env e,calldataarg args) filtered {f -> !f.isFallback }{
    uint256 alicePropositionPowerBefore=getPowerCurrent(alice,PROPOSITION_POWER());
    uint8 aliceDelegationStatusBefore=getdelegationStatus(alice);
    uint104 aliceBalanceBefore=getBalance(alice);
    uint72 aliceDelegatedPropositionBalanceBefore=getDelegatedPropositionBalance(alice);

    f(e,args);

    uint256 alicePropositionPowerAfter=getPowerCurrent(alice,PROPOSITION_POWER());
    uint8 aliceDelegationStatusAfter=getdelegationStatus(alice);
    uint104 aliceBalanceAfter=getBalance(alice);
    uint72 aliceDelegatedPropositionBalanceAfter=getDelegatedPropositionBalance(alice);

    assert alicePropositionPowerAfter>alicePropositionPowerBefore => (aliceBalanceAfter>aliceBalanceBefore || aliceDelegatedPropositionBalanceAfter>aliceDelegatedPropositionBalanceBefore || ((aliceDelegationStatusAfter ==0 || aliceDelegationStatusAfter==1) && (aliceDelegationStatusBefore==2 || aliceDelegationStatusBefore==3))) , "Proposition power can only increase if 1.Balance increases. 2. delegated Proposition balance increases. 3. undelegate Proposition power if already delegated.";
}

/* 8.Only owner of account can change his delegatee. Except in case of using "meta" functions. */

rule delegatorCanOnlyChangeDelegatee(method f,env e,calldataarg args) filtered {f -> !f.isFallback }{
    address alice;
    address delegateeBefore=getVotingDelegate(alice);
    f(e,args);
    require !(f.selector == metaDelegateByType(address,address,uint8,uint256,uint8,bytes32,bytes32).selector || f.selector == metaDelegate(address,address,uint256,uint8,bytes32,bytes32).selector );
    address delegateeAfter=getVotingDelegate(alice);

    assert delegateeBefore!=delegateeAfter => e.msg.sender==alice
    ,"Only delegator must be the one which can  change his delegatee except metaDelegate functions";
}


/* 9. if a user delegates his voting/proposition power to a new delegatee the delegatedVotingBalance/delegatedPropositionBalance of previous delegatee must reduce and the delegatedVotingBalance/delegatedPropositionBalance of new delegatee must increase accordingly/proportionately. */

rule redelegatingUpdateStateOfpreviosDelegatee( address delegateeFirst,address delegateeSecond,env e) {

    require  delegateeFirst != 0 && delegateeSecond != 0 && delegateeFirst != delegateeSecond;
    require e.msg.sender != 0 && e.msg.sender != delegateeFirst && e.msg.sender != delegateeSecond;

    uint104 balanceOfSenderBefore = getBalance(e.msg.sender);

    delegate(e, delegateeFirst);

    uint72 votingDelegatedBalanceOfdelegateeFirstBeforeDelegate = getDelegatedVotingBalance(delegateeFirst);
    uint72 propositionDelegatedBalanceOfdelegateeFirstBeforeDelegate = getDelegatedPropositionBalance(delegateeFirst);
    uint72 votingDelegatedBalanceOfdelegateeSecondBeforeDelegate = getDelegatedVotingBalance(delegateeSecond);
    uint72 propositionDelegatedBalanceOfdelegateeSecondBeforeDelegate = getDelegatedPropositionBalance(delegateeSecond);

    delegate(e, delegateeSecond);

    uint72 votingDelegatedBalanceOfdelegateeFirstAfterDelegate = getDelegatedVotingBalance(delegateeFirst);
    uint72 propositionDelegatedBalanceOfdelegateeFirstAfterDelegate = getDelegatedPropositionBalance(delegateeFirst);
    uint72 votingDelegatedBalanceOfdelegateeSecondAfterDelegate = getDelegatedVotingBalance(delegateeSecond);
    uint72 propositionDelegatedBalanceOfdelegateeSecondAfterDelegate = getDelegatedPropositionBalance(delegateeSecond);
    uint104 balanceOfSenderAfter = getBalance(e.msg.sender);

    assert votingDelegatedBalanceOfdelegateeFirstBeforeDelegate - balanceOfSenderBefore/DELEGATED_POWER_DIVIDER() == votingDelegatedBalanceOfdelegateeFirstAfterDelegate;


    assert propositionDelegatedBalanceOfdelegateeFirstBeforeDelegate - balanceOfSenderBefore/DELEGATED_POWER_DIVIDER() == propositionDelegatedBalanceOfdelegateeFirstAfterDelegate;

    assert votingDelegatedBalanceOfdelegateeSecondAfterDelegate == votingDelegatedBalanceOfdelegateeSecondBeforeDelegate + balanceOfSenderBefore/DELEGATED_POWER_DIVIDER();

    assert propositionDelegatedBalanceOfdelegateeSecondBeforeDelegate + balanceOfSenderBefore/DELEGATED_POWER_DIVIDER() == propositionDelegatedBalanceOfdelegateeSecondAfterDelegate;

    assert propositionDelegatedBalanceOfdelegateeSecondAfterDelegate == propositionDelegatedBalanceOfdelegateeSecondBeforeDelegate + balanceOfSenderBefore/DELEGATED_POWER_DIVIDER();
}

/* 10. If transfer happens between A & B then sum of delegatedVotingBalance/delegatedPropositionBalance of delegatees of A & B before transfer is same as after the transfer. */

rule sumOfDelegateeDelegatedBalanceNotChangeIfTransferHappensBetweenDelegators{
   env e; address alice=e.msg.sender;address bob;uint104 amount;
    address aliceDelegatee=getVotingDelegate(alice);
    address bobDelegatee=getVotingDelegate(bob);
    require(alice!=0 && bob!=0 && aliceDelegatee!=0 && bobDelegatee!=0 && aliceDelegatee!=alice && bobDelegatee!=bob && __checkDelegateeDelegatedVotingBalance(alice) && __checkDelegateeDelegatedVotingBalance(bob));
    uint104 aliceBalanceBefore=getBalance(alice); 
    uint104 bobBalanceBefore=getBalance(bob); 
    uint72 sumBefore=getDelegatedVotingBalance(aliceDelegatee)+getDelegatedVotingBalance(bobDelegatee);

    transfer(e,bob,to_uint256(amount));

    uint104 aliceBalanceAfter=getBalance(alice); 
    uint104 bobBalanceAfter=getBalance(bob); 

    uint72 sumAfter=getDelegatedVotingBalance(aliceDelegatee)+getDelegatedVotingBalance(bobDelegatee);
    assert aliceBalanceBefore+bobBalanceBefore==aliceBalanceAfter+bobBalanceAfter;
    assert sumBefore-sumAfter<=1 || sumAfter-sumBefore <=1;
}

function __checkDelegateeDelegatedVotingBalance(address user) returns bool{
    address userDelegatee=getVotingDelegate(user);
    return getDelegatedVotingBalance(userDelegatee) >= getBalance(user)/DELEGATED_POWER_DIVIDER();
}

/* 11. Nounce can change on only some functions. */

rule nonceChangeEffectCheck(method f,env e,calldataarg args) filtered {f -> !f.isFallback }{
    address alice;
    require(alice!=0);
    uint256 nonceBefore=getNonce(alice);
    require(nonceBefore != max_uint);
    require(getVotingDelegate(alice)!=alice && getPropositionDelegate(alice)!=alice);
    f(e,args);
    uint256 nonceAfter=getNonce(alice);

    assert nonceAfter!= nonceBefore => nonceAfter==nonceBefore+1 && (f.selector==metaDelegate(address,address,uint256,uint8,bytes32,bytes32).selector || f.selector==permit(address,address,uint256,uint256,uint8,bytes32,bytes32).selector || f.selector==metaDelegateByType(address,address,uint8,uint256,uint8,bytes32,bytes32).selector);
}

/* 12. one time delegate() is equal to two simultaneous delegateByType() with different power type. */

rule delegateIsEqualToDelegateByTypetwoTimesWithDiffParams(env e,address bob){
    address alice=e.msg.sender;
    require(alice!=0 && bob!=0 && alice!=bob);
    storage initialState=lastStorage;
    delegate(e,bob);
    mathint bobDelegatedVotingBalanceBefore= getDelegatedVotingBalance(bob);
    mathint bobDelegatedPropositionBalanceBefore= getDelegatedPropositionBalance(bob);
    mathint aliceVotingPowerBefore=getPowerCurrent(alice,VOTING_POWER());
    
    delegateByType(e,bob,VOTING_POWER()) at initialState;
    delegateByType(e,bob,PROPOSITION_POWER());
    mathint bobDelegatedVotingBalanceAfter= getDelegatedVotingBalance(bob);
    mathint bobDelegatedPropositionBalanceAfter= getDelegatedPropositionBalance(bob);
    mathint aliceVotingPowerAfter=getPowerCurrent(alice,VOTING_POWER());
    
    assert bobDelegatedVotingBalanceBefore==bobDelegatedVotingBalanceAfter && bobDelegatedPropositionBalanceBefore==bobDelegatedPropositionBalanceAfter && aliceVotingPowerBefore==aliceVotingPowerAfter;
}

/* 13. Zero balance address can delegate power to other user but it won't affect the delegatedBalance of the user. */

rule zeroBalanceUserCanDelegate(address bob,env e,method f,calldataarg args){
   address alice=e.msg.sender;
   require alice!=0;
   require(getBalance(alice)==0);
   require(bob!=0 && alice!=bob);
   uint72 _delegatedVotingBalanceOfBob=getDelegatedVotingBalance(bob);
   delegate(e,bob);
   uint72 delegatedVotingBalanceOfBob_=getDelegatedVotingBalance(bob);
   uint8 aliceDelegationStatus=getdelegationStatus(alice);
   assert aliceDelegationStatus==3 && getVotingDelegate(alice)==bob;
   assert _delegatedVotingBalanceOfBob == delegatedVotingBalanceOfBob_;
}

/* 14. If a address has zero voting power then he must have zero delegatedVotingBalance. Similarly for proposition power */

rule zeroPowerMustMeanZeroDelegatedBalance(address alice,method f,env e,calldataarg args) filtered {f -> !f.isFallback }{
    require getPowerCurrent(alice,VOTING_POWER())==0 && getDelegatedVotingBalance(alice)==0;
    require getPowerCurrent(alice,PROPOSITION_POWER())==0 && getDelegatedPropositionBalance(alice)==0;
    f(e,args);
    assert getPowerCurrent(alice,VOTING_POWER())==0 => getDelegatedVotingBalance(alice)==0;
    assert getPowerCurrent(alice,PROPOSITION_POWER())==0 => getDelegatedPropositionBalance(alice)==0;
}


// NOTE:- could not prove these rules/invariants.


/* 15. the delegatedVotingBalance of delegatee of user A must always be greater than or equal to (A's balance / 10^10) except if delegatee id 0 address. , similarly for proposition type. */

rule checkDelegateeDelegatedVotingPower(address alice,method f,env e,calldataarg args){
    address _aliceDelegatee=getVotingDelegate(alice);
    require(alice!=0 && _aliceDelegatee!=0 && alice!=_aliceDelegatee);
    require(getDelegatedVotingBalance(_aliceDelegatee) >= getBalance(alice)/DELEGATED_POWER_DIVIDER());
    f(e,args);
    address aliceDelegatee_=getVotingDelegate(alice);
    require(aliceDelegatee_!=0);

    assert getDelegatedVotingBalance(aliceDelegatee_) >= getBalance(alice)/DELEGATED_POWER_DIVIDER(); 
}

/* 16. total delegated voting balance must be  less or equal to totalSupply()/DELEGATED_POWER_DIVIDER(). */

ghost mathint sumVotingDelegatedBalance{
     init_state axiom sumVotingDelegatedBalance == 0;
}
hook Sstore _balances[KEY address user].delegatedVotingBalance uint72 balance
    (uint72 old_balance) STORAGE {
        sumVotingDelegatedBalance = sumVotingDelegatedBalance - to_mathint(old_balance) + to_mathint(balance);
    }

invariant totalVotingDelegatedEqualSupply()
    sumVotingDelegatedBalance <= totalSupply()/DELEGATED_POWER_DIVIDER()