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
    getDelegatedPropositionBalance(address user) returns (uint256) envfree
    getDelegatedVotingBalance(address user) returns (uint256) envfree
    getDelegatingProposition(address user) returns (bool) envfree
    getDelegatingVoting(address user) returns (bool) envfree
    getVotingDelegate(address user) returns (address) envfree
    getPropositionDelegate(address user) returns (address) envfree
    POWER_SCALE_FACTOR() returns (uint256) envfree
    DELEGATOR() returns (address) envfree
    DIGEST() returns (bytes32) envfree
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

rule metaDelegateWrongDelegator(uint8 type, address ws, address u, uint256 deadline, uint8 v, bytes32 r, bytes32 s) {
    env e;
    storage init = lastStorage;
    if (type==0)
        metaDelegate(e, e.msg.sender, u, deadline, v, r, s);
    else if (type==1)
        metaDelegateByType(e, e.msg.sender, u, VOTING_POWER(), deadline, v, r, s);
    else
        metaDelegateByType(e, e.msg.sender, u, PROPOSITION_POWER(), deadline, v, r, s);
    address _delegator = DELEGATOR();
    bytes32 _digest = DIGEST();

    require e.msg.sender != ws;
    if (type==0)
        metaDelegate@withrevert(e, ws, u, deadline, v, r, s) at init;
    else if (type==1)
        metaDelegateByType@withrevert(e, ws, u, VOTING_POWER(), deadline, v, r, s) at init;
    else
        metaDelegateByType@withrevert(e, ws, u, PROPOSITION_POWER(), deadline, v, r, s) at init;
    address delegator_ = DELEGATOR();
    bytes32 digest_ = DIGEST();

    assert lastReverted;
}
