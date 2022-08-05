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
    permit(address,address,uint256,uint256,uint8,bytes32,bytes32)
    getPowerCurrent(address user, uint8 delegationType) returns (uint256) envfree
    getBalance(address user) returns (uint104) envfree
    getDelegatedPropositionBalance(address user) returns (uint72) envfree
    getDelegatedVotingBalance(address user) returns (uint72) envfree
    getDelegatingProposition(address user) returns (bool) envfree
    getDelegatingVoting(address user) returns (bool) envfree
    getVotingDelegate(address user) returns (address) envfree
    getPropositionDelegate(address user) returns (address) envfree
    getDelegationState(address user) returns(uint8) envfree
    getNonce(address) returns(uint256) envfree
    getAllowance(address,address) returns (uint256) envfree
    approve(address,uint256) returns(bool)
    increaseAllowance(address,uint256) returns(bool)
    decreaseAllowance(address,uint256) returns(bool)
}

/**

    Constants

*/
// GovernancyType enum from the token contract
definition VOTING_POWER() returns uint8 = 0;
definition PROPOSITION_POWER() returns uint8 = 1;

definition DELEGATED_POWER_DIVIDER() returns uint256 = 10^10;

definition POWER_SCALE_FACTOR() returns uint256 = 10^10;

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

rule powerChangesOnTransferIfOneIsDelegateeOfOther(env e1, env e2){
    address alice = e1.msg.sender;
    address bob = e2.msg.sender;
    uint256 amount;

    address aliceVotingDelegate=getVotingDelegate(alice);
    address alicePropositionDelegate=getPropositionDelegate(alice);
    address bobVotingDelegate=getVotingDelegate(bob);
    address bobPropositionDelegate=getPropositionDelegate(bob);

    uint72 aliceDelegatedVotingPowerBefore=getDelegatedVotingBalance(alice);
    uint72 aliceDelegatedPropositionPowerBefore=getDelegatedPropositionBalance(alice);
    uint72 bobDelegatedVotingPowerBefore=getDelegatedVotingBalance(bob);
    uint72 bobDelegatedPropositionPowerBefore=getDelegatedPropositionBalance(bob);

    require(alice!= 0 && bob!= 0 && alice!=bob);
    require(aliceVotingDelegate!=alice && alicePropositionDelegate!=alice && bobVotingDelegate!=bob && bobPropositionDelegate!=bob);

    transfer(e1,bob,amount);

    uint72 aliceDelegatedVotingPowerAfter=getDelegatedVotingBalance(alice);
    uint72 aliceDelegatedPropositionPowerAfter=getDelegatedPropositionBalance(alice);
    uint72 bobDelegatedVotingPowerAfter=getDelegatedVotingBalance(bob);
    uint72 bobDelegatedPropositionPowerAfter=getDelegatedPropositionBalance(bob);

    assert aliceDelegatedVotingPowerBefore!=aliceDelegatedVotingPowerAfter => bobVotingDelegate==alice;
    assert aliceDelegatedPropositionPowerBefore!=aliceDelegatedPropositionPowerAfter => bobPropositionDelegate==alice;
    assert bobDelegatedVotingPowerAfter!=bobDelegatedVotingPowerBefore => aliceVotingDelegate==bob;
    assert bobDelegatedPropositionPowerBefore!=bobDelegatedPropositionPowerAfter => alicePropositionDelegate==bob;
}

rule powerIsEqualToBalanceAndDelegateByOthers(env e) {
    address user;

    uint256 balance = balanceOf(user);
    uint256 delegatedVotingBalance = getDelegatedVotingBalance(user);
    uint256 delegatedPropositionBalance = getDelegatedPropositionBalance(user);
    uint256 votingPower = getPowerCurrent(user, VOTING_POWER());
    uint256 propositionPower = getPowerCurrent(user, PROPOSITION_POWER());

    if(getDelegationState(user) == 0) {
        assert votingPower == balance + delegatedVotingBalance*POWER_SCALE_FACTOR();
        assert propositionPower == balance + delegatedPropositionBalance*POWER_SCALE_FACTOR();
    } else if(getDelegationState(user) == 1) {
        assert votingPower == delegatedVotingBalance*POWER_SCALE_FACTOR();
        assert propositionPower == balance + delegatedPropositionBalance*POWER_SCALE_FACTOR();
    } else if(getDelegationState(user) == 2) {
        assert votingPower == balance + delegatedVotingBalance*POWER_SCALE_FACTOR();
        assert propositionPower == delegatedPropositionBalance*POWER_SCALE_FACTOR();
    } else {
        assert votingPower == delegatedVotingBalance*POWER_SCALE_FACTOR();
        assert propositionPower == delegatedPropositionBalance*POWER_SCALE_FACTOR();
    }
}

rule ifAccountDelegateToItselfThenItIsNotDelegatingPowerToAnyone(env e) {
    address alice=e.msg.sender;

    uint256 aliceDelegatedVotingPowerBefore=getPowerCurrent(alice, VOTING_POWER());
    uint256 aliceDelegatedPropositionPowerBefore=getPowerCurrent(alice, PROPOSITION_POWER());
    uint72 aliceDelegatedVotingBalanceBefore=getDelegatedVotingBalance(alice);
    uint72 aliceDelegatedPropositionBalanceBefore=getDelegatedPropositionBalance(alice);
    address aliceVotingDelegateBefore=getVotingDelegate(alice);
    address alicePropositionDelegateBefore=getPropositionDelegate(alice);

    delegate(e, alice);

    uint256 aliceDelegatedVotingPowerAfter=getPowerCurrent(alice, VOTING_POWER());
    uint256 aliceDelegatedPropositionPowerAfter=getPowerCurrent(alice, PROPOSITION_POWER());
    uint72 aliceDelegatedVotingBalanceAfter=getDelegatedVotingBalance(alice);
    uint72 aliceDelegatedPropositionBalanceAfter=getDelegatedPropositionBalance(alice);

    assert aliceVotingDelegateBefore==0 => aliceDelegatedVotingPowerBefore==aliceDelegatedVotingPowerAfter;
    assert alicePropositionDelegateBefore==0 => aliceDelegatedPropositionPowerBefore==aliceDelegatedPropositionPowerAfter;
    assert aliceDelegatedVotingBalanceBefore==aliceDelegatedVotingBalanceAfter;
    assert aliceDelegatedPropositionBalanceBefore==aliceDelegatedPropositionBalanceAfter;

}

rule ifAccountDelegateToZeroThenItIsNotDelegatingPowerToAnyone(env e) {
    address alice=e.msg.sender;

    uint256 aliceDelegatedVotingPowerBefore=getPowerCurrent(alice, VOTING_POWER());
    uint256 aliceDelegatedPropositionPowerBefore=getPowerCurrent(alice, PROPOSITION_POWER());
    uint72 aliceDelegatedVotingBalanceBefore=getDelegatedVotingBalance(alice);
    uint72 aliceDelegatedPropositionBalanceBefore=getDelegatedPropositionBalance(alice);
    address aliceVotingDelegateBefore=getVotingDelegate(alice);
    address alicePropositionDelegateBefore=getPropositionDelegate(alice);

    delegate(e, 0);

    uint256 aliceDelegatedVotingPowerAfter=getPowerCurrent(alice, VOTING_POWER());
    uint256 aliceDelegatedPropositionPowerAfter=getPowerCurrent(alice, PROPOSITION_POWER());
    uint72 aliceDelegatedVotingBalanceAfter=getDelegatedVotingBalance(alice);
    uint72 aliceDelegatedPropositionBalanceAfter=getDelegatedPropositionBalance(alice);

    assert aliceVotingDelegateBefore==0 => aliceDelegatedVotingPowerBefore==aliceDelegatedVotingPowerAfter;
    assert alicePropositionDelegateBefore==0 => aliceDelegatedPropositionPowerBefore==aliceDelegatedPropositionPowerAfter;
    assert aliceDelegatedVotingBalanceBefore==aliceDelegatedVotingBalanceAfter;
    assert aliceDelegatedPropositionBalanceBefore==aliceDelegatedPropositionBalanceAfter;

}

rule integrityOfDelegate(env e){
    address sender=e.msg.sender;
    address delegatee;
    require delegatee!=sender && delegatee!=0;
    uint256 balanceOfSenderBefore=balanceOf(sender);
    uint72 delegatedVotingBalanceBefore=getDelegatedVotingBalance(delegatee);
    uint72 delegatedPropositionBalanceBefore=getDelegatedPropositionBalance(delegatee);
    address votingDelegateBefore=getVotingDelegate(sender);
    address propositionDelegateBefore=getPropositionDelegate(sender);
    uint256 votingPowerBefore=getPowerCurrent(delegatee,VOTING_POWER());
    uint256 propositionPowerBefore=getPowerCurrent(delegatee,PROPOSITION_POWER());

    delegate(e, delegatee);

    address votingDelegateAfter=getVotingDelegate(sender);
    address propositionDelegateAfter=getPropositionDelegate(sender);
    uint72 delegatedVotingBalanceAfter=getDelegatedVotingBalance(delegatee);
    uint72 delegatedPropositionBalanceAfter=getDelegatedPropositionBalance(delegatee);
    uint256 votingPowerAfter=getPowerCurrent(delegatee,VOTING_POWER());
    uint256 propositionPowerAfter=getPowerCurrent(delegatee,PROPOSITION_POWER());

    assert delegatee!=votingDelegateBefore => delegatedVotingBalanceBefore+balanceOfSenderBefore/10^10==delegatedVotingBalanceAfter;
    assert delegatee!=propositionDelegateBefore => delegatedPropositionBalanceBefore+balanceOfSenderBefore/10^10==delegatedPropositionBalanceAfter;
    assert delegatee!=votingDelegateBefore => votingPowerBefore+normalize(balanceOfSenderBefore)==votingPowerAfter;
    assert delegatee!=propositionDelegateBefore => propositionPowerBefore+normalize(balanceOfSenderBefore)==propositionPowerAfter;
    assert votingDelegateAfter==delegatee;
    assert propositionDelegateAfter==delegatee;
}

rule integrityOfDelegateByType(env e){
    address sender=e.msg.sender;
    address delegatee;
    require delegatee!=sender && delegatee!=0;
    uint256 balanceOfSenderBefore=balanceOf(sender);
    uint72 delegatedVotingBalanceBefore=getDelegatedVotingBalance(delegatee);
    uint72 delegatedPropositionBalanceBefore=getDelegatedPropositionBalance(delegatee);
    address votingDelegateBefore=getVotingDelegate(sender);
    address propositionDelegateBefore=getPropositionDelegate(sender);
    uint256 votingPowerBefore=getPowerCurrent(delegatee,VOTING_POWER());
    uint256 propositionPowerBefore=getPowerCurrent(delegatee,PROPOSITION_POWER());

    delegateByType(e, delegatee, VOTING_POWER());
    delegateByType(e, delegatee, PROPOSITION_POWER());

    address votingDelegateAfter=getVotingDelegate(sender);
    address propositionDelegateAfter=getPropositionDelegate(sender);
    uint72 delegatedVotingBalanceAfter=getDelegatedVotingBalance(delegatee);
    uint72 delegatedPropositionBalanceAfter=getDelegatedPropositionBalance(delegatee);
    uint256 votingPowerAfter=getPowerCurrent(delegatee,VOTING_POWER());
    uint256 propositionPowerAfter=getPowerCurrent(delegatee,PROPOSITION_POWER());

    assert delegatee!=votingDelegateBefore => delegatedVotingBalanceBefore+balanceOfSenderBefore/10^10==delegatedVotingBalanceAfter;
    assert delegatee!=propositionDelegateBefore => delegatedPropositionBalanceBefore+balanceOfSenderBefore/10^10==delegatedPropositionBalanceAfter;
    assert delegatee!=votingDelegateBefore => votingPowerBefore+normalize(balanceOfSenderBefore)==votingPowerAfter;
    assert delegatee!=propositionDelegateBefore => propositionPowerBefore+normalize(balanceOfSenderBefore)==propositionPowerAfter;
    assert votingDelegateAfter==delegatee;
    assert propositionDelegateAfter==delegatee;
}

rule compareDelegateAndDelegateByType(env e) {
    address delegatee;
    storage initialStorage=lastStorage;

    delegate(e, delegatee);

    address votingDelegateBefore=getVotingDelegate(e.msg.sender);
    address propositionDelegateBefore=getPropositionDelegate(e.msg.sender);
    uint256 votingPowerBefore=getPowerCurrent(delegatee, VOTING_POWER());
    uint256 propositionPowerBefore=getPowerCurrent(delegatee, PROPOSITION_POWER());
    uint72 delegatedVotingBalanceBefore=getDelegatedVotingBalance(delegatee);
    uint72 delegatedPropositionBalanceBefore=getDelegatedPropositionBalance(delegatee);

    delegateByType(e, delegatee, VOTING_POWER()) at initialStorage;
    delegateByType(e, delegatee, PROPOSITION_POWER());

    address votingDelegateAfter=getVotingDelegate(e.msg.sender);
    address propositionDelegateAfter=getPropositionDelegate(e.msg.sender);
    uint256 votingPowerAfter=getPowerCurrent(delegatee, VOTING_POWER());
    uint256 propositionPowerAfter=getPowerCurrent(delegatee, PROPOSITION_POWER());
    uint72 delegatedVotingBalanceAfter=getDelegatedVotingBalance(delegatee);
    uint72 delegatedPropositionBalanceAfter=getDelegatedPropositionBalance(delegatee);

    assert votingDelegateBefore==votingDelegateAfter;
    assert propositionDelegateBefore==propositionDelegateAfter;
    assert votingPowerBefore==votingPowerAfter;
    assert propositionPowerBefore==propositionPowerAfter;
    assert delegatedVotingBalanceBefore==delegatedVotingBalanceAfter;
    assert delegatedPropositionBalanceBefore==delegatedPropositionBalanceAfter;
}

rule userCanNotDelegateToMoreThanOneUser(env e){
    address sender=e.msg.sender;
    address user1;
    address user2;

    require user1 != sender && user2 != sender && user1 != user2;
    require sender != 0 && user1 != 0 && user2 != 0;

    uint256 balanceOfSender=getBalance(sender);

    delegate(e, user1);

    uint72 oldDelegateVotingBalanceBefore=getDelegatedVotingBalance(user1);
    uint72 oldDelegatePropositionBalanceBefore=getDelegatedPropositionBalance(user1);
    uint72 newDelegateVotingBalanceBefore=getDelegatedVotingBalance(user2);
    uint72 newDelegatePropositionBalanceBefore=getDelegatedPropositionBalance(user2);

    delegate(e, user2);

    uint72 oldDelegateVotingBalanceAfter=getDelegatedVotingBalance(user1);
    uint72 oldDelegatePropositionBalanceAfter=getDelegatedPropositionBalance(user1);
    uint72 newDelegateVotingBalanceAfter=getDelegatedVotingBalance(user2);
    uint72 newDelegatePropositionBalanceAfter=getDelegatedPropositionBalance(user2);

    assert oldDelegateVotingBalanceAfter + balanceOfSender/DELEGATED_POWER_DIVIDER() == oldDelegateVotingBalanceBefore;
    assert oldDelegatePropositionBalanceAfter + balanceOfSender/DELEGATED_POWER_DIVIDER() == oldDelegatePropositionBalanceBefore;
    assert newDelegateVotingBalanceBefore + balanceOfSender/DELEGATED_POWER_DIVIDER() == newDelegateVotingBalanceAfter;
    assert newDelegatePropositionBalanceBefore + balanceOfSender/DELEGATED_POWER_DIVIDER() == newDelegatePropositionBalanceAfter;
}

rule delegationToZeroOrItselfDoesNotDelegateToAnyone(env e) {
    address sender=e.msg.sender;
    address to;

    require to==0 || to==sender;

    uint256 votingPowerBeforeDelegate=getPowerCurrent(sender, VOTING_POWER());
    address votingDelegateBeforeDelegate=getVotingDelegate(sender);

    require votingDelegateBeforeDelegate==0;

    delegate(e, to);

    uint256 votingPowerAfterDelegate=getPowerCurrent(sender, VOTING_POWER());
    address votingDelegateAfterDelegate=getVotingDelegate(sender);

    assert votingDelegateAfterDelegate==0;
    assert votingPowerBeforeDelegate==votingPowerAfterDelegate;
}

rule powerEqualsBalanceIfNoDelegation(env e){
    address user;
    uint256 votingPower=getPowerCurrent(user,VOTING_POWER());
    uint256 propositionPower=getPowerCurrent(user,PROPOSITION_POWER());

    require getDelegatedVotingBalance(user)==0 && getDelegatedPropositionBalance(user)==0;
    require getDelegationState(user)==0;

    assert votingPower==balanceOf(user);
    assert propositionPower==balanceOf(user);
}

rule delegateNoInterfereWithAnotherUser(env e){
    address delegatee;
    address anotherUser;
    require delegatee != anotherUser;
    require e.msg.sender != anotherUser;

    address votingDelegateBefore=getVotingDelegate(anotherUser);
    address propositionDelegateBefore=getPropositionDelegate(anotherUser);
    uint72 delegatedVotingBalanceBefore=getDelegatedVotingBalance(anotherUser);
    uint72 delegatedPropositionBalanceBefore=getDelegatedPropositionBalance(anotherUser);
    uint256 votingPowerBefore=getPowerCurrent(anotherUser,VOTING_POWER());
    uint256 propositionPowerBefore=getPowerCurrent(anotherUser,PROPOSITION_POWER());

    require getVotingDelegate(e.msg.sender)!=anotherUser && getPropositionDelegate(e.msg.sender)!=anotherUser;

    delegate(e, delegatee);

    address votingDelegateAfter=getVotingDelegate(anotherUser);
    address propositionDelegateAfter=getPropositionDelegate(anotherUser);
    uint72 delegatedVotingBalanceAfter=getDelegatedVotingBalance(anotherUser);
    uint72 delegatedPropositionBalanceAfter=getDelegatedPropositionBalance(anotherUser);
    uint256 votingPowerAfter=getPowerCurrent(anotherUser,VOTING_POWER());
    uint256 propositionPowerAfter=getPowerCurrent(anotherUser,PROPOSITION_POWER());

    assert votingDelegateBefore==votingDelegateAfter;
    assert propositionDelegateBefore==propositionDelegateAfter;
    assert delegatedVotingBalanceBefore==delegatedVotingBalanceAfter;
    assert delegatedPropositionBalanceBefore==delegatedPropositionBalanceAfter;
    assert votingPowerBefore==votingPowerAfter;
    assert propositionPowerBefore==propositionPowerAfter;
}

rule delegationNeedsToBeFullAndNotPortion(env e) {
    address delegatee;
    require e.msg.sender != delegatee;
    require e.msg.sender != 0 && delegatee != 0;

    require getDelegatedVotingBalance(delegatee)==0 && getDelegatedPropositionBalance(delegatee)==0;
    require getVotingDelegate(e.msg.sender) != delegatee && getPropositionDelegate(e.msg.sender) != delegatee;

    uint256 balance=balanceOf(e.msg.sender);

    delegate(e, delegatee);

    assert getDelegatedVotingBalance(delegatee)==balance/DELEGATED_POWER_DIVIDER();
    assert getDelegatedPropositionBalance(delegatee)==balance/DELEGATED_POWER_DIVIDER();
}

rule delegateCanOnlyBeChangedByDelegateFunctions(env e) {
    method f;
    calldataarg args;
    address user;

    address votingDelegateBefore=getVotingDelegate(user);
    address propositionDelegateBefore=getPropositionDelegate(user);

    f(e, args);

    address votingDelegateAfter=getVotingDelegate(user);
    address propositionDelegateAfter=getPropositionDelegate(user);

    assert votingDelegateBefore!=votingDelegateAfter&&propositionDelegateBefore!=propositionDelegateAfter => 
    f.selector==delegate(address).selector || f.selector==metaDelegate(address,address,uint256,uint8,bytes32,bytes32).selector;

    assert votingDelegateBefore!=votingDelegateAfter || propositionDelegateBefore!=propositionDelegateAfter =>
    f.selector==delegateByType(address,uint8).selector || f.selector==metaDelegateByType(address,address,uint8,uint256,uint8,bytes32,bytes32).selector ||
    f.selector==delegate(address).selector || f.selector==metaDelegate(address,address,uint256,uint8,bytes32,bytes32).selector;
}

rule metaFunctionsCanAllowOtherUsersToDelegateChanges(env e) {
    method f;
    calldataarg args;
    address user;

    address votingDelegateBefore=getVotingDelegate(user);
    address propositionDelegateBefore=getPropositionDelegate(user);

    f(e, args);

    address votingDelegateAfter=getVotingDelegate(user);
    address propositionDelegateAfter=getPropositionDelegate(user);

    assert (votingDelegateBefore != getVotingDelegate(user) || propositionDelegateAfter != getPropositionDelegate(user)) &&
        (f.selector != metaDelegateByType(address,address,uint8,uint256,uint8,bytes32,bytes32).selector && f.selector != metaDelegate(address,address,uint256,uint8,bytes32,bytes32).selector)
        => e.msg.sender==user;
}

rule nonceCanOnlyBeChangedByCertainFunction(env e) {
    address user;
    calldataarg args;
    method f;

    uint256 nonceBefore=getNonce(user);

    f(e, args);

    uint256 nonceAfter=getNonce(user);

    assert nonceBefore != nonceAfter => f.selector==permit(address,address,uint256,uint256,uint8,bytes32,bytes32).selector ||
    f.selector==metaDelegateByType(address,address,uint8,uint256,uint8,bytes32,bytes32).selector ||
    f.selector==metaDelegate(address,address,uint256,uint8,bytes32,bytes32).selector;
}

invariant addressZeroDoesNotHaveVotingPower() 
    balanceOf(0)==0 && getDelegatedVotingBalance(0)==0 && getPowerCurrent(0, VOTING_POWER())==0

invariant addressZeroDoesNotHavePropositionPower()
    balanceOf(0)==0 && getDelegatedPropositionBalance(0)==0 && getPowerCurrent(0, PROPOSITION_POWER())==0

rule votingDelegationDoesNotInterfereWithPropositionDelegate(env e) {
    address user1;
    address user2;
    require user1 != user2 && e.msg.sender != user1 && e.msg.sender != user2;

    address propositionDelegateBefore=getPropositionDelegate(user2);
    uint72 delegatedPropositionBalanceBefore=getDelegatedPropositionBalance(user2);
    uint256 propositionPowerBefore=getPowerCurrent(user2, PROPOSITION_POWER());

    delegateByType(e, user1, VOTING_POWER());

    address propositionDelegateAfter=getPropositionDelegate(user2);
    uint72 delegatedPropositionBalanceAfter=getDelegatedPropositionBalance(user2);
    uint256 propositionPowerAfter=getPowerCurrent(user2, PROPOSITION_POWER());

    assert propositionDelegateBefore==propositionDelegateAfter;
    assert delegatedPropositionBalanceBefore==delegatedPropositionBalanceAfter;
    assert propositionPowerBefore==propositionPowerAfter;

}

rule integrityOfPermit(env e){
    address owner;
    address spender;
    uint256 value;
    uint256 deadline;
    uint8 v;
    bytes32 r;
    bytes32 s;

    uint256 allowanceBefore=getAllowance(owner,spender);
    uint256 nonceBefore=getNonce(owner);

    permit(e,owner,spender,value,deadline,v,r,s);

    uint256 allowanceAfter=getAllowance(owner,spender);
    uint256 nonceAfter=getNonce(owner);

    assert allowanceAfter==value;
    assert nonceBefore<max_uint256 => nonceAfter==nonceBefore + 1;
}

rule allowanceStateChange(env e){
    address owner;
    address user;
    method f;
    calldataarg args;

    uint256 allowanceBefore=getAllowance(owner,user);
    f(e, args);
    uint256 allowanceAfter=getAllowance(owner,user);

    assert allowanceBefore!=allowanceAfter => f.selector==approve(address,uint256).selector 
    || f.selector==increaseAllowance(address,uint256).selector
    || f.selector==decreaseAllowance(address,uint256).selector
    || f.selector==transferFrom(address,address,uint256).selector
    || f.selector==permit(address,address,uint256,uint256,uint8,bytes32,bytes32).selector;
}

rule transferReducesVotingPowerAndPropositionPowerOfSender(env e) {
    address user1=e.msg.sender;
    address user2;
    uint256 amount;
    require user1!=user2 && user1!=0 && user2!=0 && getVotingDelegate(user2)!=user1 && getPropositionDelegate(user2)!=user1;
    uint256 balanceBefore=balanceOf(user1);
    uint256 votingPowerBefore=getPowerCurrent(user1,VOTING_POWER());
    uint256 propositionPowerBefore=getPowerCurrent(user1,PROPOSITION_POWER());

    transfer(e, user2, amount);

    uint256 balanceAfter=balanceOf(user1);
    uint256 votingPowerAfter=getPowerCurrent(user1,VOTING_POWER());
    uint256 propositionPowerAfter=getPowerCurrent(user1,PROPOSITION_POWER());

    assert balanceAfter + amount==balanceBefore;
    assert votingPowerBefore>=votingPowerAfter;
    assert propositionPowerBefore>=propositionPowerAfter;
}

rule sumOfDelegateeOfUsersInvolvedInTransferStaysTheSame(env e){
    address user1=e.msg.sender;
    address user2;
    uint256 amount;
    address delegatee1Before=getVotingDelegate(user1);
    address delegatee2Before=getVotingDelegate(user2);
    mathint sumOfVotingBalanceOfDelegateesBefore=getDelegatedVotingBalance(delegatee1Before)+getDelegatedVotingBalance(delegatee2Before);

    transfer(e, user2, amount);

    address delegatee1After=getVotingDelegate(user1);
    address delegatee2After=getVotingDelegate(user2);
    mathint sumOfVotingBalanceOfDelegateesAfter=getDelegatedVotingBalance(delegatee1After)+getDelegatedVotingBalance(delegatee2After);

    assert sumOfVotingBalanceOfDelegateesBefore-sumOfVotingBalanceOfDelegateesAfter<=1 || sumOfVotingBalanceOfDelegateesAfter-sumOfVotingBalanceOfDelegateesBefore <=1;
    assert delegatee1Before==delegatee1After;
    assert delegatee2Before==delegatee2After;
}

rule someoneWithAllowanceCanChangeVotingPowerOfSender(env e){
    address recevier;
    uint256 amount;
    require getAllowance(e.msg.sender, recevier)>=amount;
    require getVotingDelegate(recevier)!=e.msg.sender && getPropositionDelegate(recevier)!=e.msg.sender;
    require e.msg.sender!=0 && recevier!=0 && e.msg.sender!=recevier;

    uint256 votingPowerBefore=getPowerCurrent(e.msg.sender,VOTING_POWER());
    uint256 propositionPowerBefore=getPowerCurrent(e.msg.sender,PROPOSITION_POWER());

    transferFrom(e, e.msg.sender, recevier, amount);

    uint256 votingPowerAfter=getPowerCurrent(e.msg.sender,VOTING_POWER());
    uint256 propositionPowerAfter=getPowerCurrent(e.msg.sender,PROPOSITION_POWER());

    assert votingPowerAfter<=votingPowerBefore;
    assert propositionPowerAfter<=propositionPowerBefore;
}









/**

    Testing correctness of delegate(). An example of a unit test

*/

rule delegateCorrectness(address bob) {
    env e;
    // delegate not to self or to zero
    require bob != e.msg.sender && bob != 0;

    uint256 bobDelegatedBalance=getDelegatedVotingBalance(bob);
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