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
    getPowersCurrent(address user) returns (uint256, uint256) envfree
    getBalance(address user) returns (uint104) envfree
    getDelegatedPropositionBalance(address user) returns (uint72) envfree
    getDelegatedVotingBalance(address user) returns (uint72) envfree
    getDelegatingProposition(address user) returns (bool) envfree
    getDelegatingVoting(address user) returns (bool) envfree
    getVotingDelegate(address user) returns (address) envfree
    getPropositionDelegate(address user) returns (address) envfree
}

function getPublicUserState(address user) returns uint256[] { // (uint256, uint256, uint104, uint72, uint72, bool, bool, address, address) { 
    // uint256 i = 0;
    // // uint256[9] result = [i, i, i, i, i, i, i, i, i];
    // return [
    //     getPowerCurrent(user, VOTING_POWER()),
    //     getPowerCurrent(user, PROPOSITION_POWER()),
    //     uint256(getBalance(user)),
    //     // getDelegatedPropositionBalance(user),
    //     // getDelegatedVotingBalance(user),
    //     // getDelegatingVoting(user),
    //     // getDelegatingProposition(user),
    //     // getVotingDelegate(user),
    //     // getPropositionDelegate(user)
    // ];
    return [
        getPowerCurrent(user, VOTING_POWER()),
        getPowerCurrent(user, PROPOSITION_POWER()),
        balanceOf(user)];
}

function sameUserState(uint256[] s1, uint256[] s2) returns bool {
    return s1[0] == s2[0] && s1[1] == s2[1] && s1[2] == s2[2];
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


// ghost mapping (address => uint256) nonces {
//     init_state axiom forall address addr . nonces[addr] == 0;
// }

// hook Sstore _nonces[KEY address user] uint256 nonce STORAGE {
//     nonces[user] = nonce;
// }

// rule successfulTransferOnlyFromOwnerOrApproved(address from, address to, uint256 amount) {
//     env e;
//     uint256 balanceFromBefore = balanceOf(from);
//     uint256 allowanceBefore = allowance(from, e.msg.sender);
//     transferFrom(e, from, to, amount);
//     uint256 balanceFromAfter = balanceOf(from);
//     assert balanceFromAfter < balanceFromBefore => 
//         e.msg.sender == from ||
//         allowanceBefore >= amount;
// }

// rule playAroundWithEcrecover(address delegator, address delegatee, uint256 deadline, uint8 v, bytes32 r, bytes32 s) {
//     bytes32 digest = keccak256(
//         abi.encodePacked(
//             "\x19\x01",
//             DOMAIN_SEPARATOR(),
//             keccak256(abi.encode(DELEGATE_TYPEHASH(), delegator, delegatee, nonces[delegator], deadline))
//         )
//     );
//     require ecrecover(digest, v, r, s) == delegator;
//     metaDelegate(delegator, delegatee, deadline, v, r, s);
//     assert getVotingDelegate(delegator) == delegatee;
// }

// this isn't true: hash collision may occur
// rule metaDelegateNonRepeatable(env e, address delegator, address delegatee, uint256 deadline, uint8 v, bytes32 r, bytes32 s) {
//     metaDelegate(e, delegator, delegatee, deadline, v, r, s);
//     metaDelegate@withrevert(e, delegator, delegatee, deadline, v, r, s);
//     assert lastReverted;
// }

rule metaDelegateInvalidAfterDeadline(env e, address delegator, address delegatee, uint256 deadline, uint8 v, bytes32 r, bytes32 s) {
    require e.block.timestamp > deadline;
    metaDelegate@withrevert(e, delegator, delegatee, deadline, v, r, s);
    assert lastReverted;
}

rule metaDelegateSameAsDelegate(env eD, env eMD, address delegator, address delegatee, uint256 deadline, uint8 v, bytes32 r, bytes32 s) {
    storage initialStorage = lastStorage;
    address anyUser;
    // require delegator == eD.msg.sender;
    delegate(eD, delegatee);
    uint256[] userStateD = getPublicUserState(anyUser);

    metaDelegate(eMD, delegator, delegatee, deadline, v, r, s) at initialStorage;
    uint256[] userStateMD = getPublicUserState(anyUser);

    assert sameUserState(userStateD, userStateMD);
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

invariant getPowersAgreesWithGetPower(address addr)
    (getPowerCurrent(addr, VOTING_POWER()), getPowerCurrent(addr, PROPOSITION_POWER())) == getPowersCurrent(addr)

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

invariant onlyVotingPowerSourcesAreBalanceAndDelegation(address addr)
    getPowerCurrent(addr, VOTING_POWER()) == getVotingBalance(addr) + getScaledDelegatedVotingPower(addr)

invariant onlyPropositionPowerSourcesAreBalanceAndDelegation(address addr)
    getPowerCurrent(addr, PROPOSITION_POWER()) == getPropositionBalance(addr) + getScaledDelegatedPropositionPower(addr)

invariant delegatingVotingIffVotingDelegateIsNonZero(address addr)
    getDelegatingVoting(addr) <=> getVotingDelegate(addr) != 0

invariant delegatingPropositionIffPropositionDelegateIsNonZero(address addr)
    getDelegatingProposition(addr) <=> getPropositionDelegate(addr) != 0