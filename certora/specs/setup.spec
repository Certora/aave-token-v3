/**

    Setup for writing rules for Aave Token v3 

*/

/**
    Public methods from the AaveTokenV3Harness.sol
*/

methods {
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
    getDelegationState(address user) returns (uint8) envfree
    getVotingDelegate(address user) returns (address) envfree
    getPropositionDelegate(address user) returns (address) envfree
    ecrecover_wrapper(bytes32 digest, uint8 v, bytes32 r, bytes32 s) returns (address) envfree
    computeMetaDelegateHash(address delegator,  address delegatee,  uint256 deadline, uint256 nonce) returns (bytes32) envfree
    _nonces(address addr) returns (uint256) envfree
}

function getPublicAddresUserState(method f, address user) returns address {
    if (f.selector == getVotingDelegate(address).selector) {
        return getVotingDelegate(user);
    }   
    if (f.selector == getPropositionDelegate(address).selector) {
        return getPropositionDelegate(user);
    }
    return 0;
}

function getPublicNumericUserState(method f, address user) returns uint256 {
    if (f.selector == getBalance(address).selector) {
        return getBalance(user);
    } 
    if (f.selector == getDelegatedPropositionBalance(address).selector) {
        return getDelegatedPropositionBalance(user);
    }
    if (f.selector == getDelegatedVotingBalance(address).selector) {
        return getDelegatedPropositionBalance(user);
    }
    if (f.selector == getDelegatingProposition(address).selector) {
        return getDelegatingProposition(user) ? to_uint256(1) : to_uint256(0);
    }
    if (f.selector == getDelegatingVoting(address).selector) {
        return getDelegatingVoting(user) ? to_uint256(1) : to_uint256(0);
    }    
    return 0;
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

function getScaledDelegatedVotingPower(address addr) returns uint256 {
    return to_uint256(DELEGATED_POWER_DIVIDER() * getDelegatedVotingBalance(addr));
}

function getScaledDelegatedPropositionPower(address addr) returns uint256 {
    return to_uint256(DELEGATED_POWER_DIVIDER() * getDelegatedPropositionBalance(addr));
}

function getVotingBalance(address addr) returns uint256 {
    return getDelegatingVoting(addr) ? 0 : balanceOf(addr);
}

function getPropositionBalance(address addr) returns uint256 {
    return getDelegatingProposition(addr) ? 0 : balanceOf(addr);
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

rule metaDelegateOnlyCallableWithProperlySignedArguments(env e, address delegator, address delegatee, uint256 deadline, uint8 v, bytes32 r, bytes32 s) {
    require ecrecover_wrapper(computeMetaDelegateHash(delegator, delegatee, deadline, _nonces(delegator)), v, r, s) != delegator;
    metaDelegate@withrevert(e, delegator, delegatee, deadline, v, r, s);
    assert lastReverted;
}

rule metaDelegateNonRepeatable(env e, address delegator, address delegatee, uint256 deadline, uint8 v, bytes32 r, bytes32 s) {
    uint256 nonce = _nonces(delegator);
    bytes32 hash1 = computeMetaDelegateHash(delegator, delegatee, deadline, nonce);
    bytes32 hash2 = computeMetaDelegateHash(delegator, delegatee, deadline, nonce+1);
    // assume no hash collisions
    require hash1 != hash2;
    // assume first call is properly signed
    require ecrecover_wrapper(hash1, v, r, s) == delegator;
    // assume ecrecover is sane: cannot sign two different messages with the same (v,r,s)
    require ecrecover_wrapper(hash2, v, r, s) != ecrecover_wrapper(hash1, v, r, s);
    metaDelegate(e, delegator, delegatee, deadline, v, r, s);
    metaDelegate@withrevert(e, delegator, delegatee, deadline, v, r, s);
    assert lastReverted;
}

rule metaDelegateInvalidAfterDeadline(env e, address delegator, address delegatee, uint256 deadline, uint8 v, bytes32 r, bytes32 s) {
    require e.block.timestamp > deadline;
    metaDelegate@withrevert(e, delegator, delegatee, deadline, v, r, s);
    assert lastReverted;
}

rule metaDelegateSameAsDelegate(env eD, env eMD, address delegator, address delegatee, uint256 deadline, uint8 v, bytes32 r, bytes32 s) {
    storage initialStorage = lastStorage;
    method f;
    address user;
    require delegator == eD.msg.sender;
    delegate(eD, delegatee);
    uint256 numericUserStateD = getPublicNumericUserState(f, user);
    address addressUserStateD = getPublicAddresUserState(f, user);

    metaDelegate(eMD, delegator, delegatee, deadline, v, r, s) at initialStorage;
    uint256 numericUserStateMD = getPublicNumericUserState(f, user);
    address addressUserStateMD = getPublicAddresUserState(f, user);
    
    assert numericUserStateD == numericUserStateMD &&
        addressUserStateD == addressUserStateMD;
}


rule delegateByBothTypesSameAsDelegate(env e1, env e2, env e3, address delegatee) {
        storage initialStorage = lastStorage;
    method f;
    address user;
    require e1.msg.sender == e2.msg.sender && e1.msg.sender == e3.msg.sender;
    delegate(e1, delegatee);
    uint256 numericUserStateD = getPublicNumericUserState(f, user);
    address addressUserStateD = getPublicAddresUserState(f, user);

    delegateByType(e2, delegatee, VOTING_POWER());
    delegateByType(e3, delegatee, PROPOSITION_POWER());
    uint256 numericUserStateMD = getPublicNumericUserState(f, user);
    address addressUserStateMD = getPublicAddresUserState(f, user);
    
    assert numericUserStateD == numericUserStateMD &&
        addressUserStateD == addressUserStateMD;
}

// rule delegationToZeroReclaimsFullPower(env e) {
//     delegate(e, 0);
//     assert getVotingDelegate(e.msg.sender) == e.msg.sender &&
//         getPropositionDelegate(e.msg.sender) == e.msg.sender;
// }

rule delegationToZeroAlwaysPossible(env e) {
    requireInvariant delegationStateFlagIsLessThan4(e.msg.sender);
    //TODO prove it
    require getVotingDelegate(e.msg.sender) != 0 =>
        getDelegatedVotingBalance(getVotingDelegate(e.msg.sender)) >= balanceOf(e.msg.sender) / DELEGATED_POWER_DIVIDER();
    require getPropositionDelegate(e.msg.sender) != 0 =>
        getDelegatedPropositionBalance(getPropositionDelegate(e.msg.sender)) >= balanceOf(e.msg.sender) / DELEGATED_POWER_DIVIDER();
    require e.msg.value == 0;
    delegate@withrevert(e, 0);
    assert !lastReverted;
}

rule getPowersAgreesWithGetPower(address addr) {
    assert (getPowerCurrent(addr, VOTING_POWER()), getPowerCurrent(addr, PROPOSITION_POWER())) ==
        getPowersCurrent(addr);
}

rule onlyVotingPowerSourcesAreBalanceAndDelegation(address addr) {
    assert getPowerCurrent(addr, VOTING_POWER()) ==
        getVotingBalance(addr) + getScaledDelegatedVotingPower(addr);
}

rule onlyPropositionPowerSourcesAreBalanceAndDelegation(address addr) {
    assert getPowerCurrent(addr, PROPOSITION_POWER()) ==
        getPropositionBalance(addr) + getScaledDelegatedPropositionPower(addr);
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

invariant nullAddressZeroBalance()
    balanceOf(0) == 0

invariant nullAdressZeroVotingPower() 
    getPowerCurrent(0, VOTING_POWER()) == 0 {
        preserved {
            requireInvariant nullAddressZeroBalance();
        }
    }

invariant nullAdressZeroPropositionPower()
    getPowerCurrent(0, PROPOSITION_POWER()) == 0 {
        preserved {
            requireInvariant nullAddressZeroBalance();
        }
    }

invariant neverSelfDelegate(address addr)
    addr != 0 => getVotingDelegate(addr) != addr

invariant delegatingVotingIffVotingDelegateIsNonZero(address addr)
    getDelegatingVoting(addr) <=> getVotingDelegate(addr) != 0

invariant delegatingPropositionIffPropositionDelegateIsNonZero(address addr)
    getDelegatingProposition(addr) <=> getPropositionDelegate(addr) != 0

invariant delegationStateFlagIsLessThan4(address addr)
    getDelegationState(addr) < 4

invariant delegatedVotingBalanceOfDelegateeGreaterThanDelegatorBalanceLemma(address delegator1, address delegator2, address delegatee)
    getDelegatedVotingBalance(delegatee) >= getBalance(delegator1) / DELEGATED_POWER_DIVIDER() + getBalance(delegator2) / DELEGATED_POWER_DIVIDER() {
        preserved {
            requireInvariant delegatingVotingIffVotingDelegateIsNonZero(delegator1);
            requireInvariant delegatingVotingIffVotingDelegateIsNonZero(delegator2);
            require delegatee != 0;
            require getVotingDelegate(delegator1) == delegatee;
            require getVotingDelegate(delegator2) == delegatee;
        }
    }