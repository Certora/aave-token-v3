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

/**

    Testing correctness of delegate(). An example of a unit test

*/
// rule delegateCorrectness(address bob) {
//     env e;
//     // delegate not to self or to zero
//     require bob != e.msg.sender && bob != 0;

//     uint256 bobDelegatedBalance = getDelegatedVotingBalance(bob);
//     // avoid unrealistic delegated balance
//     require(bobDelegatedBalance < MAX_DELEGATED_BALANCE());
    
//     // verify that the sender doesn't already delegate to bob
//     address delegateBefore = getVotingDelegate(e.msg.sender);
//     require delegateBefore != bob;
//     uint256 bobVotingPowerBefore = getPowerCurrent(bob, VOTING_POWER());
//     uint256 delegatorBalance = balanceOf(e.msg.sender);
//     delegate(e, bob);
//     // test the delegate indeed has changed to bob
//     address delegateAfter = getVotingDelegate(e.msg.sender);
//     assert delegateAfter == bob;
//     // test the delegate's new voting power
//     uint256 bobVotingPowerAfter = getPowerCurrent(bob, VOTING_POWER());
//     assert bobVotingPowerAfter == bobVotingPowerBefore + normalize(delegatorBalance);
// }

invariant isVotingDelegated(address a)
    (getDelegatingVoting(a)==false <=> getVotingDelegate(a) == 0)
    && (getDelegatingVoting(a)==true => getVotingDelegate(a) != a)
    filtered {
        f -> !f.isView
    }

invariant isPropositionDelegated(address a)
    (getDelegatingProposition(a)==false <=> getPropositionDelegate(a) == 0)
    && (getDelegatingProposition(a)==true => getPropositionDelegate(a) != a)
    filtered {
        f -> !f.isView
    }

invariant VotingPowerVsDelegatedVotingBalance(address a)
    getDelegatingVoting(a)==true => getPowerCurrent(a, VOTING_POWER()) == getDelegatedVotingBalance(a)
    && getDelegatingVoting(a)==false => getPowerCurrent(a, VOTING_POWER()) == getDelegatedVotingBalance(a) + balanceOf(a)
    filtered {
        f -> !f.isView
    }

invariant PropositionPowerVsDelegatedPropositionBalance(address a)
    getDelegatingProposition(a)==true => getPowerCurrent(a, PROPOSITION_POWER()) == getDelegatedPropositionBalance(a)
    && getDelegatingProposition(a)==false => getPowerCurrent(a, PROPOSITION_POWER()) == getDelegatedPropositionBalance(a) + balanceOf(a)
    filtered {
        f -> !f.isView
    }

rule delegateCorrectness(address u) {
    env e;
    require e.msg.sender != 0;

    address _uVotingDelegate = getVotingDelegate(u);
    address _uPropositionDelegate = getPropositionDelegate(u);
    uint256 _uDelegatorBalance = balanceOf(u);
    uint256 _uDelegatedVotingBalance = getDelegatedVotingBalance(u);
    require(_uDelegatedVotingBalance < MAX_DELEGATED_BALANCE());
    uint256 _uDelegatedPropositionBalance = getDelegatedPropositionBalance(u);
    require(_uDelegatedPropositionBalance < MAX_DELEGATED_BALANCE());
    uint256 _uVotingPower = getPowerCurrent(u, VOTING_POWER());
    uint256 _uPropositionPower = getPowerCurrent(u, PROPOSITION_POWER());
    
    address _sVotingDelegate = getVotingDelegate(e.msg.sender);
    address _sPropositionDelegate = getPropositionDelegate(e.msg.sender);
    uint256 _sDelegatorBalance = balanceOf(e.msg.sender);
    uint256 _sDelegatedVotingBalance = getDelegatedVotingBalance(e.msg.sender);
    require(_sDelegatedVotingBalance < MAX_DELEGATED_BALANCE());
    uint256 _sDelegatedPropositionBalance = getDelegatedPropositionBalance(e.msg.sender);
    require(_sDelegatedPropositionBalance < MAX_DELEGATED_BALANCE());
    uint256 _sVotingPower = getPowerCurrent(e.msg.sender, VOTING_POWER());
    uint256 _sPropositionPower = getPowerCurrent(e.msg.sender, PROPOSITION_POWER());

    requireInvariant isVotingDelegated(e.msg.sender);
    requireInvariant isPropositionDelegated(e.msg.sender);

    delegate(e, u);

    address uVotingDelegate_ = getVotingDelegate(u);
    address uPropositionDelegate_ = getPropositionDelegate(u);
    uint256 uDelegatorBalance_ = balanceOf(u);
    uint256 uDelegatedVotingBalance_ = getDelegatedVotingBalance(u);
    require(uDelegatedVotingBalance_ < MAX_DELEGATED_BALANCE());
    uint256 uDelegatedPropositionBalance_ = getDelegatedPropositionBalance(u);
    require(uDelegatedPropositionBalance_ < MAX_DELEGATED_BALANCE());
    uint256 uVotingPower_ = getPowerCurrent(u, VOTING_POWER());
    uint256 uPropositionPower_ = getPowerCurrent(u, PROPOSITION_POWER());
    
    address sVotingDelegate_ = getVotingDelegate(e.msg.sender);
    address sPropositionDelegate_ = getPropositionDelegate(e.msg.sender);
    uint256 sDelegatorBalance_ = balanceOf(e.msg.sender);
    uint256 sDelegatedVotingBalance_ = getDelegatedVotingBalance(e.msg.sender);
    require(sDelegatedVotingBalance_ < MAX_DELEGATED_BALANCE());
    uint256 sDelegatedPropositionBalance_ = getDelegatedPropositionBalance(e.msg.sender);
    require(sDelegatedPropositionBalance_ < MAX_DELEGATED_BALANCE());
    uint256 sVotingPower_ = getPowerCurrent(e.msg.sender, VOTING_POWER());
    uint256 sPropositionPower_ = getPowerCurrent(e.msg.sender, PROPOSITION_POWER());

    assert _sDelegatorBalance == sDelegatorBalance_
        && _sDelegatedVotingBalance == sDelegatedVotingBalance_
        && _sDelegatedPropositionBalance == sDelegatedPropositionBalance_;
    assert _uDelegatorBalance == uDelegatorBalance_;

    if (u == e.msg.sender || u == 0) {
        assert sVotingDelegate_ == 0; 
        assert sPropositionDelegate_ == 0; 
        if (u==0) {
            assert uVotingPower_ == _uVotingPower;
            assert uDelegatedVotingBalance_ == _uDelegatedVotingBalance;
            assert uPropositionPower_ == _uPropositionPower;
            assert uDelegatedPropositionBalance_ == _uDelegatedPropositionBalance;        
        }
        if (_sVotingDelegate!=sVotingDelegate_) {
            assert sVotingPower_ == _sVotingPower + sDelegatorBalance_;        
        } else {
            assert _sVotingPower == sVotingPower_;
        }
        if (_sPropositionDelegate!=sPropositionDelegate_) {
            assert sPropositionPower_ == _sPropositionPower + sDelegatorBalance_;
        } else {
            assert _sPropositionPower == sPropositionPower_;
        }
    } else {
        assert _uVotingDelegate == uVotingDelegate_
            && _uPropositionDelegate == uPropositionDelegate_;
        assert sVotingDelegate_ == u; 
        assert sPropositionDelegate_ == u; 

        if (_sVotingDelegate!=sVotingDelegate_) {
            assert uVotingPower_ == _uVotingPower + normalize(sDelegatorBalance_);
            assert uDelegatedVotingBalance_ == _uDelegatedVotingBalance + normalize(sDelegatorBalance_);        
        } else {
            assert uVotingPower_ == _uVotingPower;
            assert uDelegatedVotingBalance_ == _uDelegatedVotingBalance;
        }
        if (_sVotingDelegate==0) {
            assert _sVotingPower == sVotingPower_ + sDelegatorBalance_;        
        } else {
            assert _sVotingPower == sVotingPower_;
        }

        if (_sPropositionDelegate!=sPropositionDelegate_) {
            assert uPropositionPower_ == _uPropositionPower + normalize(sDelegatorBalance_);
            assert uDelegatedPropositionBalance_ == _uDelegatedPropositionBalance + normalize(sDelegatorBalance_);        
        } else {
            assert uPropositionPower_ == _uPropositionPower;
            assert uDelegatedPropositionBalance_ == _uDelegatedPropositionBalance;        
        }
        if (_sPropositionDelegate==0) {
            assert _sPropositionPower == sPropositionPower_ + sDelegatorBalance_;
        } else {
            assert _sPropositionPower == sPropositionPower_;
        }

    }    
}

rule delegateVotingOnly(address u) {
    env e;
    require e.msg.sender != 0;

    address _uVotingDelegate = getVotingDelegate(u);
    address _uPropositionDelegate = getPropositionDelegate(u);
    uint256 _uDelegatorBalance = balanceOf(u);
    uint256 _uDelegatedVotingBalance = getDelegatedVotingBalance(u);
    require(_uDelegatedVotingBalance < MAX_DELEGATED_BALANCE());
    uint256 _uDelegatedPropositionBalance = getDelegatedPropositionBalance(u);
    require(_uDelegatedPropositionBalance < MAX_DELEGATED_BALANCE());
    uint256 _uVotingPower = getPowerCurrent(u, VOTING_POWER());
    uint256 _uPropositionPower = getPowerCurrent(u, PROPOSITION_POWER());
    
    address _sVotingDelegate = getVotingDelegate(e.msg.sender);
    address _sPropositionDelegate = getPropositionDelegate(e.msg.sender);
    uint256 _sDelegatorBalance = balanceOf(e.msg.sender);
    uint256 _sDelegatedVotingBalance = getDelegatedVotingBalance(e.msg.sender);
    require(_sDelegatedVotingBalance < MAX_DELEGATED_BALANCE());
    uint256 _sDelegatedPropositionBalance = getDelegatedPropositionBalance(e.msg.sender);
    require(_sDelegatedPropositionBalance < MAX_DELEGATED_BALANCE());
    uint256 _sVotingPower = getPowerCurrent(e.msg.sender, VOTING_POWER());
    uint256 _sPropositionPower = getPowerCurrent(e.msg.sender, PROPOSITION_POWER());

    requireInvariant isVotingDelegated(e.msg.sender);
    requireInvariant isPropositionDelegated(e.msg.sender);

    delegateByType(e, u, VOTING_POWER());

    address uVotingDelegate_ = getVotingDelegate(u);
    address uPropositionDelegate_ = getPropositionDelegate(u);
    uint256 uDelegatorBalance_ = balanceOf(u);
    uint256 uDelegatedVotingBalance_ = getDelegatedVotingBalance(u);
    require(uDelegatedVotingBalance_ < MAX_DELEGATED_BALANCE());
    uint256 uDelegatedPropositionBalance_ = getDelegatedPropositionBalance(u);
    require(uDelegatedPropositionBalance_ < MAX_DELEGATED_BALANCE());
    uint256 uVotingPower_ = getPowerCurrent(u, VOTING_POWER());
    uint256 uPropositionPower_ = getPowerCurrent(u, PROPOSITION_POWER());
    
    address sVotingDelegate_ = getVotingDelegate(e.msg.sender);
    address sPropositionDelegate_ = getPropositionDelegate(e.msg.sender);
    uint256 sDelegatorBalance_ = balanceOf(e.msg.sender);
    uint256 sDelegatedVotingBalance_ = getDelegatedVotingBalance(e.msg.sender);
    require(sDelegatedVotingBalance_ < MAX_DELEGATED_BALANCE());
    uint256 sDelegatedPropositionBalance_ = getDelegatedPropositionBalance(e.msg.sender);
    require(sDelegatedPropositionBalance_ < MAX_DELEGATED_BALANCE());
    uint256 sVotingPower_ = getPowerCurrent(e.msg.sender, VOTING_POWER());
    uint256 sPropositionPower_ = getPowerCurrent(e.msg.sender, PROPOSITION_POWER());

    assert _sDelegatorBalance == sDelegatorBalance_
        && _sDelegatedVotingBalance == sDelegatedVotingBalance_
        && _sDelegatedPropositionBalance == sDelegatedPropositionBalance_
        && _sPropositionPower == sPropositionPower_
        && _sPropositionDelegate == sPropositionDelegate_;
    
    assert _uDelegatorBalance == uDelegatorBalance_
        && _uPropositionDelegate == uPropositionDelegate_
        && _uPropositionPower == uPropositionPower_
        && _uDelegatedPropositionBalance == uDelegatedPropositionBalance_;        
    
    if (u == e.msg.sender || u == 0) {
        assert sVotingDelegate_ == 0; 
        if (u==0) {
            assert uVotingPower_ == _uVotingPower;
            assert uDelegatedVotingBalance_ == _uDelegatedVotingBalance;
        }
        if (_sVotingDelegate!=sVotingDelegate_) {
            assert sVotingPower_ == _sVotingPower + sDelegatorBalance_;        
        } else {
            assert _sVotingPower == sVotingPower_;
        }
    } else {
        assert _uVotingDelegate == uVotingDelegate_;
        assert sVotingDelegate_ == u; 

        if (_sVotingDelegate!=sVotingDelegate_) {
            assert uVotingPower_ == _uVotingPower + normalize(sDelegatorBalance_);
            assert uDelegatedVotingBalance_ == _uDelegatedVotingBalance + normalize(sDelegatorBalance_);        
        } else {
            assert uVotingPower_ == _uVotingPower;
            assert uDelegatedVotingBalance_ == _uDelegatedVotingBalance;
        }
        if (_sVotingDelegate==0) {
            assert _sVotingPower == sVotingPower_ + sDelegatorBalance_;        
        } else {
            assert _sVotingPower == sVotingPower_;
        }
    }    
}


rule delegatePropositionOnly(address u) {
    env e;
    require e.msg.sender != 0;

    address _uVotingDelegate = getVotingDelegate(u);
    address _uPropositionDelegate = getPropositionDelegate(u);
    uint256 _uDelegatorBalance = balanceOf(u);
    uint256 _uDelegatedVotingBalance = getDelegatedVotingBalance(u);
    require(_uDelegatedVotingBalance < MAX_DELEGATED_BALANCE());
    uint256 _uDelegatedPropositionBalance = getDelegatedPropositionBalance(u);
    require(_uDelegatedPropositionBalance < MAX_DELEGATED_BALANCE());
    uint256 _uVotingPower = getPowerCurrent(u, VOTING_POWER());
    uint256 _uPropositionPower = getPowerCurrent(u, PROPOSITION_POWER());
    
    address _sVotingDelegate = getVotingDelegate(e.msg.sender);
    address _sPropositionDelegate = getPropositionDelegate(e.msg.sender);
    uint256 _sDelegatorBalance = balanceOf(e.msg.sender);
    uint256 _sDelegatedVotingBalance = getDelegatedVotingBalance(e.msg.sender);
    require(_sDelegatedVotingBalance < MAX_DELEGATED_BALANCE());
    uint256 _sDelegatedPropositionBalance = getDelegatedPropositionBalance(e.msg.sender);
    require(_sDelegatedPropositionBalance < MAX_DELEGATED_BALANCE());
    uint256 _sVotingPower = getPowerCurrent(e.msg.sender, VOTING_POWER());
    uint256 _sPropositionPower = getPowerCurrent(e.msg.sender, PROPOSITION_POWER());

    requireInvariant isVotingDelegated(e.msg.sender);
    requireInvariant isPropositionDelegated(e.msg.sender);

    delegateByType(e, u, PROPOSITION_POWER());

    address uVotingDelegate_ = getVotingDelegate(u);
    address uPropositionDelegate_ = getPropositionDelegate(u);
    uint256 uDelegatorBalance_ = balanceOf(u);
    uint256 uDelegatedVotingBalance_ = getDelegatedVotingBalance(u);
    require(uDelegatedVotingBalance_ < MAX_DELEGATED_BALANCE());
    uint256 uDelegatedPropositionBalance_ = getDelegatedPropositionBalance(u);
    require(uDelegatedPropositionBalance_ < MAX_DELEGATED_BALANCE());
    uint256 uVotingPower_ = getPowerCurrent(u, VOTING_POWER());
    uint256 uPropositionPower_ = getPowerCurrent(u, PROPOSITION_POWER());
    
    address sVotingDelegate_ = getVotingDelegate(e.msg.sender);
    address sPropositionDelegate_ = getPropositionDelegate(e.msg.sender);
    uint256 sDelegatorBalance_ = balanceOf(e.msg.sender);
    uint256 sDelegatedVotingBalance_ = getDelegatedVotingBalance(e.msg.sender);
    require(sDelegatedVotingBalance_ < MAX_DELEGATED_BALANCE());
    uint256 sDelegatedPropositionBalance_ = getDelegatedPropositionBalance(e.msg.sender);
    require(sDelegatedPropositionBalance_ < MAX_DELEGATED_BALANCE());
    uint256 sVotingPower_ = getPowerCurrent(e.msg.sender, VOTING_POWER());
    uint256 sPropositionPower_ = getPowerCurrent(e.msg.sender, PROPOSITION_POWER());

    assert _sDelegatorBalance == sDelegatorBalance_
        && _sDelegatedVotingBalance == sDelegatedVotingBalance_
        && _sDelegatedPropositionBalance == sDelegatedPropositionBalance_
        && _sVotingPower == sVotingPower_
        && _sVotingDelegate == sVotingDelegate_;
    
    assert _uDelegatorBalance == uDelegatorBalance_
        && _uVotingDelegate == uVotingDelegate_
        && _uVotingPower == uVotingPower_
        && _uDelegatedVotingBalance == uDelegatedVotingBalance_;        
    
    if (u == e.msg.sender || u == 0) {
        assert sPropositionDelegate_ == 0; 
        if (u==0) {
            assert uPropositionPower_ == _uPropositionPower;
            assert uDelegatedPropositionBalance_ == _uDelegatedPropositionBalance;
        }
        if (_sPropositionDelegate!=sPropositionDelegate_) {
            assert sPropositionPower_ == _sPropositionPower + sDelegatorBalance_;        
        } else {
            assert _sPropositionPower == sPropositionPower_;
        }
    } else {
        assert _uPropositionDelegate == uPropositionDelegate_;
        assert sPropositionDelegate_ == u; 

        if (_sPropositionDelegate!=sPropositionDelegate_) {
            assert uPropositionPower_ == _uPropositionPower + normalize(sDelegatorBalance_);
            assert uDelegatedPropositionBalance_ == _uDelegatedPropositionBalance + normalize(sDelegatorBalance_);        
        } else {
            assert uPropositionPower_ == _uPropositionPower;
            assert uDelegatedPropositionBalance_ == _uDelegatedPropositionBalance;
        }
        if (_sPropositionDelegate==0) {
            assert _sPropositionPower == sPropositionPower_ + sDelegatorBalance_;        
        } else {
            assert _sPropositionPower == sPropositionPower_;
        }
    }    
}

rule delegateImpactToOther(address u, address o) {
    env e;
    require o!=u && o!=e.msg.sender && e.msg.sender!=0 && o!=0;

    address _oVotingDelegate = getVotingDelegate(o);
    address _oPropositionDelegate = getPropositionDelegate(o);
    uint256 _oDelegatorBalance = balanceOf(o);
    address _oDelegateBefore = getVotingDelegate(o);
    uint256 _oDelegatedVotingBalance = getDelegatedVotingBalance(o);
    require(_oDelegatedVotingBalance < MAX_DELEGATED_BALANCE());
    uint256 _oDelegatedPropositionBalance = getDelegatedPropositionBalance(o);
    require(_oDelegatedPropositionBalance < MAX_DELEGATED_BALANCE());
    uint256 _oVotingPower = getPowerCurrent(o, VOTING_POWER());
    uint256 _oPropositionPower = getPowerCurrent(o, PROPOSITION_POWER());
        
    address _sVotingDelegate = getVotingDelegate(e.msg.sender);
    address _sPropositionDelegate = getPropositionDelegate(e.msg.sender);
    uint256 sDelegatorBalance = balanceOf(e.msg.sender);

    requireInvariant isVotingDelegated(e.msg.sender);
    requireInvariant isPropositionDelegated(e.msg.sender);

    delegate(e, u);

    address oVotingDelegate_ = getVotingDelegate(o);
    address oPropositionDelegate_ = getPropositionDelegate(o);
    uint256 oDelegatorBalance_ = balanceOf(o);
    address oDelegateBefore_ = getVotingDelegate(o);
    uint256 oDelegatedVotingBalance_ = getDelegatedVotingBalance(o);
    require(oDelegatedVotingBalance_ < MAX_DELEGATED_BALANCE());
    uint256 oDelegatedPropositionBalance_ = getDelegatedPropositionBalance(o);
    require(oDelegatedPropositionBalance_ < MAX_DELEGATED_BALANCE());
    uint256 oVotingPower_ = getPowerCurrent(o, VOTING_POWER());
    uint256 oPropositionPower_ = getPowerCurrent(o, PROPOSITION_POWER());
    
    address sVotingDelegate_ = getVotingDelegate(e.msg.sender);
    address sPropositionDelegate_ = getPropositionDelegate(e.msg.sender);

    assert _oVotingDelegate == oVotingDelegate_
        && _oPropositionDelegate == oPropositionDelegate_
        && _oDelegatorBalance == oDelegatorBalance_;

    if (o == _sVotingDelegate && o!= sVotingDelegate_)  {
        assert oVotingPower_ == _oVotingPower - normalize(sDelegatorBalance);
        assert oDelegatedVotingBalance_ == _oDelegatedVotingBalance - normalize(sDelegatorBalance);
    } else {
        assert oVotingPower_ == _oVotingPower;
        assert oDelegatedVotingBalance_ == _oDelegatedVotingBalance;
    }

    if (o == _sPropositionDelegate && o!= sPropositionDelegate_) {
        assert oPropositionPower_ == _oPropositionPower - normalize(sDelegatorBalance);
        assert oDelegatedPropositionBalance_ == _oDelegatedPropositionBalance - normalize(sDelegatorBalance);
    } else {
        assert oPropositionPower_ == _oPropositionPower;
        assert oDelegatedPropositionBalance_ == _oDelegatedPropositionBalance;
    }
}

rule delegateEquivalence(address u) {
    env e;
    storage init = lastStorage;

    delegateByType(e, u, VOTING_POWER());
    delegateByType(e, u, PROPOSITION_POWER());

    address _uVotingDelegate = getVotingDelegate(u);
    address _uPropositionDelegate = getPropositionDelegate(u);
    uint256 _uDelegatorBalance = balanceOf(u);
    uint256 _uDelegatedVotingBalance = getDelegatedVotingBalance(u);
    require(_uDelegatedVotingBalance < MAX_DELEGATED_BALANCE());
    uint256 _uDelegatedPropositionBalance = getDelegatedPropositionBalance(u);
    require(_uDelegatedPropositionBalance < MAX_DELEGATED_BALANCE());
    uint256 _uVotingPower = getPowerCurrent(u, VOTING_POWER());
    uint256 _uPropositionPower = getPowerCurrent(u, PROPOSITION_POWER());
    
    address _sVotingDelegate = getVotingDelegate(e.msg.sender);
    address _sPropositionDelegate = getPropositionDelegate(e.msg.sender);
    uint256 _sDelegatorBalance = balanceOf(e.msg.sender);
    uint256 _sDelegatedVotingBalance = getDelegatedVotingBalance(e.msg.sender);
    require(_sDelegatedVotingBalance < MAX_DELEGATED_BALANCE());
    uint256 _sDelegatedPropositionBalance = getDelegatedPropositionBalance(e.msg.sender);
    require(_sDelegatedPropositionBalance < MAX_DELEGATED_BALANCE());
    uint256 _sVotingPower = getPowerCurrent(e.msg.sender, VOTING_POWER());
    uint256 _sPropositionPower = getPowerCurrent(e.msg.sender, PROPOSITION_POWER());

    delegate(e, u) at init;

    address uVotingDelegate_ = getVotingDelegate(u);
    address uPropositionDelegate_ = getPropositionDelegate(u);
    uint256 uDelegatorBalance_ = balanceOf(u);
    uint256 uDelegatedVotingBalance_ = getDelegatedVotingBalance(u);
    require(uDelegatedVotingBalance_ < MAX_DELEGATED_BALANCE());
    uint256 uDelegatedPropositionBalance_ = getDelegatedPropositionBalance(u);
    require(uDelegatedPropositionBalance_ < MAX_DELEGATED_BALANCE());
    uint256 uVotingPower_ = getPowerCurrent(u, VOTING_POWER());
    uint256 uPropositionPower_ = getPowerCurrent(u, PROPOSITION_POWER());
    
    address sVotingDelegate_ = getVotingDelegate(e.msg.sender);
    address sPropositionDelegate_ = getPropositionDelegate(e.msg.sender);
    uint256 sDelegatorBalance_ = balanceOf(e.msg.sender);
    uint256 sDelegatedVotingBalance_ = getDelegatedVotingBalance(e.msg.sender);
    require(sDelegatedVotingBalance_ < MAX_DELEGATED_BALANCE());
    uint256 sDelegatedPropositionBalance_ = getDelegatedPropositionBalance(e.msg.sender);
    require(sDelegatedPropositionBalance_ < MAX_DELEGATED_BALANCE());
    uint256 sVotingPower_ = getPowerCurrent(e.msg.sender, VOTING_POWER());
    uint256 sPropositionPower_ = getPowerCurrent(e.msg.sender, PROPOSITION_POWER());

    assert _uVotingDelegate == uVotingDelegate_
        && _uPropositionDelegate == uPropositionDelegate_
        && _uDelegatorBalance == uDelegatorBalance_
        && _uDelegatedVotingBalance == uDelegatedVotingBalance_
        && _uDelegatedPropositionBalance == uDelegatedPropositionBalance_
        && _uVotingPower == uVotingPower_
        && _uPropositionPower == uPropositionPower_;

    assert _sVotingDelegate == sVotingDelegate_
        && _sPropositionDelegate == sPropositionDelegate_
        && _sDelegatorBalance == sDelegatorBalance_
        && _sDelegatedVotingBalance == sDelegatedVotingBalance_
        && _sDelegatedPropositionBalance == sDelegatedPropositionBalance_
        && _sVotingPower == sVotingPower_
        && _sPropositionPower == sPropositionPower_;   
}


rule delegateidempotency(address u) {
    env e;

    delegate(e, u);

    address _uVotingDelegate = getVotingDelegate(u);
    address _uPropositionDelegate = getPropositionDelegate(u);
    uint256 _uDelegatorBalance = balanceOf(u);
    uint256 _uDelegatedVotingBalance = getDelegatedVotingBalance(u);
    require(_uDelegatedVotingBalance < MAX_DELEGATED_BALANCE());
    uint256 _uDelegatedPropositionBalance = getDelegatedPropositionBalance(u);
    require(_uDelegatedPropositionBalance < MAX_DELEGATED_BALANCE());
    uint256 _uVotingPower = getPowerCurrent(u, VOTING_POWER());
    uint256 _uPropositionPower = getPowerCurrent(u, PROPOSITION_POWER());
    
    address _sVotingDelegate = getVotingDelegate(e.msg.sender);
    address _sPropositionDelegate = getPropositionDelegate(e.msg.sender);
    uint256 _sDelegatorBalance = balanceOf(e.msg.sender);
    uint256 _sDelegatedVotingBalance = getDelegatedVotingBalance(e.msg.sender);
    require(_sDelegatedVotingBalance < MAX_DELEGATED_BALANCE());
    uint256 _sDelegatedPropositionBalance = getDelegatedPropositionBalance(e.msg.sender);
    require(_sDelegatedPropositionBalance < MAX_DELEGATED_BALANCE());
    uint256 _sVotingPower = getPowerCurrent(e.msg.sender, VOTING_POWER());
    uint256 _sPropositionPower = getPowerCurrent(e.msg.sender, PROPOSITION_POWER());

    delegate(e, u);

    address uVotingDelegate_ = getVotingDelegate(u);
    address uPropositionDelegate_ = getPropositionDelegate(u);
    uint256 uDelegatorBalance_ = balanceOf(u);
    uint256 uDelegatedVotingBalance_ = getDelegatedVotingBalance(u);
    require(uDelegatedVotingBalance_ < MAX_DELEGATED_BALANCE());
    uint256 uDelegatedPropositionBalance_ = getDelegatedPropositionBalance(u);
    require(uDelegatedPropositionBalance_ < MAX_DELEGATED_BALANCE());
    uint256 uVotingPower_ = getPowerCurrent(u, VOTING_POWER());
    uint256 uPropositionPower_ = getPowerCurrent(u, PROPOSITION_POWER());
    
    address sVotingDelegate_ = getVotingDelegate(e.msg.sender);
    address sPropositionDelegate_ = getPropositionDelegate(e.msg.sender);
    uint256 sDelegatorBalance_ = balanceOf(e.msg.sender);
    uint256 sDelegatedVotingBalance_ = getDelegatedVotingBalance(e.msg.sender);
    require(sDelegatedVotingBalance_ < MAX_DELEGATED_BALANCE());
    uint256 sDelegatedPropositionBalance_ = getDelegatedPropositionBalance(e.msg.sender);
    require(sDelegatedPropositionBalance_ < MAX_DELEGATED_BALANCE());
    uint256 sVotingPower_ = getPowerCurrent(e.msg.sender, VOTING_POWER());
    uint256 sPropositionPower_ = getPowerCurrent(e.msg.sender, PROPOSITION_POWER());

    assert _uVotingDelegate == uVotingDelegate_
        && _uPropositionDelegate == uPropositionDelegate_
        && _uDelegatorBalance == uDelegatorBalance_
        && _uDelegatedVotingBalance == uDelegatedVotingBalance_
        && _uDelegatedPropositionBalance == uDelegatedPropositionBalance_
        && _uVotingPower == uVotingPower_
        && _uPropositionPower == uPropositionPower_;

    assert _sVotingDelegate == sVotingDelegate_
        && _sPropositionDelegate == sPropositionDelegate_
        && _sDelegatorBalance == sDelegatorBalance_
        && _sDelegatedVotingBalance == sDelegatedVotingBalance_
        && _sDelegatedPropositionBalance == sDelegatedPropositionBalance_
        && _sVotingPower == sVotingPower_
        && _sPropositionPower == sPropositionPower_;   
}

rule metaDelegateEquivalence(uint8 type, address u, uint256 deadline, uint8 v, bytes32 r, bytes32 s) {
    env e;
    storage init = lastStorage;

    if (type==0)
        delegate(e, u);
    else if (type==1)
        delegateByType(e, u, VOTING_POWER());
    else 
        delegateByType(e, u, PROPOSITION_POWER());

    address _uVotingDelegate = getVotingDelegate(u);
    address _uPropositionDelegate = getPropositionDelegate(u);
    uint256 _uDelegatorBalance = balanceOf(u);
    uint256 _uDelegatedVotingBalance = getDelegatedVotingBalance(u);
    require(_uDelegatedVotingBalance < MAX_DELEGATED_BALANCE());
    uint256 _uDelegatedPropositionBalance = getDelegatedPropositionBalance(u);
    require(_uDelegatedPropositionBalance < MAX_DELEGATED_BALANCE());
    uint256 _uVotingPower = getPowerCurrent(u, VOTING_POWER());
    uint256 _uPropositionPower = getPowerCurrent(u, PROPOSITION_POWER());
    
    address _sVotingDelegate = getVotingDelegate(e.msg.sender);
    address _sPropositionDelegate = getPropositionDelegate(e.msg.sender);
    uint256 _sDelegatorBalance = balanceOf(e.msg.sender);
    uint256 _sDelegatedVotingBalance = getDelegatedVotingBalance(e.msg.sender);
    require(_sDelegatedVotingBalance < MAX_DELEGATED_BALANCE());
    uint256 _sDelegatedPropositionBalance = getDelegatedPropositionBalance(e.msg.sender);
    require(_sDelegatedPropositionBalance < MAX_DELEGATED_BALANCE());
    uint256 _sVotingPower = getPowerCurrent(e.msg.sender, VOTING_POWER());
    uint256 _sPropositionPower = getPowerCurrent(e.msg.sender, PROPOSITION_POWER());

    if (type==0)
        metaDelegate(e, e.msg.sender, u, deadline, v, r, s) at init;
    else if (type==1)
        metaDelegateByType(e, e.msg.sender, u, VOTING_POWER(), deadline, v, r, s) at init;
    else
        metaDelegateByType(e, e.msg.sender, u, PROPOSITION_POWER(), deadline, v, r, s) at init;

    address uVotingDelegate_ = getVotingDelegate(u);
    address uPropositionDelegate_ = getPropositionDelegate(u);
    uint256 uDelegatorBalance_ = balanceOf(u);
    uint256 uDelegatedVotingBalance_ = getDelegatedVotingBalance(u);
    require(uDelegatedVotingBalance_ < MAX_DELEGATED_BALANCE());
    uint256 uDelegatedPropositionBalance_ = getDelegatedPropositionBalance(u);
    require(uDelegatedPropositionBalance_ < MAX_DELEGATED_BALANCE());
    uint256 uVotingPower_ = getPowerCurrent(u, VOTING_POWER());
    uint256 uPropositionPower_ = getPowerCurrent(u, PROPOSITION_POWER());
    
    address sVotingDelegate_ = getVotingDelegate(e.msg.sender);
    address sPropositionDelegate_ = getPropositionDelegate(e.msg.sender);
    uint256 sDelegatorBalance_ = balanceOf(e.msg.sender);
    uint256 sDelegatedVotingBalance_ = getDelegatedVotingBalance(e.msg.sender);
    require(sDelegatedVotingBalance_ < MAX_DELEGATED_BALANCE());
    uint256 sDelegatedPropositionBalance_ = getDelegatedPropositionBalance(e.msg.sender);
    require(sDelegatedPropositionBalance_ < MAX_DELEGATED_BALANCE());
    uint256 sVotingPower_ = getPowerCurrent(e.msg.sender, VOTING_POWER());
    uint256 sPropositionPower_ = getPowerCurrent(e.msg.sender, PROPOSITION_POWER());

    assert _uVotingDelegate == uVotingDelegate_
        && _uPropositionDelegate == uPropositionDelegate_
        && _uDelegatorBalance == uDelegatorBalance_
        && _uDelegatedVotingBalance == uDelegatedVotingBalance_
        && _uDelegatedPropositionBalance == uDelegatedPropositionBalance_
        && _uVotingPower == uVotingPower_
        && _uPropositionPower == uPropositionPower_;

    assert _sVotingDelegate == sVotingDelegate_
        && _sPropositionDelegate == sPropositionDelegate_
        && _sDelegatorBalance == sDelegatorBalance_
        && _sDelegatedVotingBalance == sDelegatedVotingBalance_
        && _sDelegatedPropositionBalance == sDelegatedPropositionBalance_
        && _sVotingPower == sVotingPower_
        && _sPropositionPower == sPropositionPower_;   
}

rule delegateReversability(address u, address o) {
    env e;

    requireInvariant isVotingDelegated(e.msg.sender);
    requireInvariant isPropositionDelegated(e.msg.sender);

    address _uVotingDelegate = getVotingDelegate(u);
    address _uPropositionDelegate = getPropositionDelegate(u);
    uint256 _uDelegatorBalance = balanceOf(u);
    uint256 _uDelegatedVotingBalance = getDelegatedVotingBalance(u);
    require(_uDelegatedVotingBalance < MAX_DELEGATED_BALANCE());
    uint256 _uDelegatedPropositionBalance = getDelegatedPropositionBalance(u);
    require(_uDelegatedPropositionBalance < MAX_DELEGATED_BALANCE());
    uint256 _uVotingPower = getPowerCurrent(u, VOTING_POWER());
    uint256 _uPropositionPower = getPowerCurrent(u, PROPOSITION_POWER());
    
    address _sVotingDelegate = getVotingDelegate(e.msg.sender);
    address _sPropositionDelegate = getPropositionDelegate(e.msg.sender);
    uint256 _sDelegatorBalance = balanceOf(e.msg.sender);
    uint256 _sDelegatedVotingBalance = getDelegatedVotingBalance(e.msg.sender);
    require(_sDelegatedVotingBalance < MAX_DELEGATED_BALANCE());
    uint256 _sDelegatedPropositionBalance = getDelegatedPropositionBalance(e.msg.sender);
    require(_sDelegatedPropositionBalance < MAX_DELEGATED_BALANCE());
    uint256 _sVotingPower = getPowerCurrent(e.msg.sender, VOTING_POWER());
    uint256 _sPropositionPower = getPowerCurrent(e.msg.sender, PROPOSITION_POWER());

    require u == _sVotingDelegate;
    require u == _sPropositionDelegate;

    delegate(e, o);
    delegate(e, u);

    address uVotingDelegate_ = getVotingDelegate(u);
    address uPropositionDelegate_ = getPropositionDelegate(u);
    uint256 uDelegatorBalance_ = balanceOf(u);
    uint256 uDelegatedVotingBalance_ = getDelegatedVotingBalance(u);
    require(uDelegatedVotingBalance_ < MAX_DELEGATED_BALANCE());
    uint256 uDelegatedPropositionBalance_ = getDelegatedPropositionBalance(u);
    require(uDelegatedPropositionBalance_ < MAX_DELEGATED_BALANCE());
    uint256 uVotingPower_ = getPowerCurrent(u, VOTING_POWER());
    uint256 uPropositionPower_ = getPowerCurrent(u, PROPOSITION_POWER());
    
    address sVotingDelegate_ = getVotingDelegate(e.msg.sender);
    address sPropositionDelegate_ = getPropositionDelegate(e.msg.sender);
    uint256 sDelegatorBalance_ = balanceOf(e.msg.sender);
    uint256 sDelegatedVotingBalance_ = getDelegatedVotingBalance(e.msg.sender);
    require(sDelegatedVotingBalance_ < MAX_DELEGATED_BALANCE());
    uint256 sDelegatedPropositionBalance_ = getDelegatedPropositionBalance(e.msg.sender);
    require(sDelegatedPropositionBalance_ < MAX_DELEGATED_BALANCE());
    uint256 sVotingPower_ = getPowerCurrent(e.msg.sender, VOTING_POWER());
    uint256 sPropositionPower_ = getPowerCurrent(e.msg.sender, PROPOSITION_POWER());

    assert _uVotingDelegate == uVotingDelegate_
        && _uPropositionDelegate == uPropositionDelegate_
        && _uDelegatorBalance == uDelegatorBalance_
        && _uDelegatedVotingBalance == uDelegatedVotingBalance_
        && _uDelegatedPropositionBalance == uDelegatedPropositionBalance_
        && _uVotingPower == uVotingPower_
        && _uPropositionPower == uPropositionPower_;

    assert _sVotingDelegate == sVotingDelegate_
        && _sPropositionDelegate == sPropositionDelegate_
        && _sDelegatorBalance == sDelegatorBalance_
        && _sDelegatedVotingBalance == sDelegatedVotingBalance_
        && _sDelegatedPropositionBalance == sDelegatedPropositionBalance_
        && _sVotingPower == sVotingPower_
        && _sPropositionPower == sPropositionPower_;   
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

rule metaDelegateWrongDelegatee(uint8 type, address u, address wu, uint256 deadline, uint8 v, bytes32 r, bytes32 s) {
    env e;
    require v==27 || v==28;
    storage init = lastStorage;
    if (type==0)
        metaDelegate(e, e.msg.sender, u, deadline, v, r, s);
    else if (type==1)
        metaDelegateByType(e, e.msg.sender, u, VOTING_POWER(), deadline, v, r, s);
    else
        metaDelegateByType(e, e.msg.sender, u, PROPOSITION_POWER(), deadline, v, r, s);
    
    require wu != u;
    if (type==0)
        metaDelegate@withrevert(e, e.msg.sender, wu, deadline, v, r, s) at init;
    else if (type==1)
        metaDelegateByType@withrevert(e, e.msg.sender, wu, VOTING_POWER(), deadline, v, r, s) at init;
    else
        metaDelegateByType@withrevert(e, e.msg.sender, wu, PROPOSITION_POWER(), deadline, v, r, s) at init;
    assert lastReverted;
}

rule metaDelegatePassDeadline(uint8 type, address u, uint256 deadline, uint8 v, bytes32 r, bytes32 s) {
    env e;
    require v==27 || v==28;
    storage init = lastStorage;
    if (type==0)
        metaDelegate(e, e.msg.sender, u, deadline, v, r, s);
    else if (type==1)
        metaDelegateByType(e, e.msg.sender, u, VOTING_POWER(), deadline, v, r, s);
    else
        metaDelegateByType(e, e.msg.sender, u, PROPOSITION_POWER(), deadline, v, r, s);
    
    env e1;
    require e1.block.timestamp > deadline;

    if (type==0)
        metaDelegate@withrevert(e1, e1.msg.sender, u, deadline, v, r, s) at init;
    else if (type==1)
        metaDelegateByType@withrevert(e1, e1.msg.sender, u, VOTING_POWER(), deadline, v, r, s) at init;
    else
        metaDelegateByType@withrevert(e1, e1.msg.sender, u, PROPOSITION_POWER(), deadline, v, r, s) at init;
    assert lastReverted;
}

rule metaDelegateWrongType(uint8 type, address u, uint256 deadline, uint8 v, bytes32 r, bytes32 s) {
    env e;
    require v==27 || v==28;
    storage init = lastStorage;
    if (type==0)
        metaDelegateByType(e, e.msg.sender, u, VOTING_POWER(), deadline, v, r, s);
    else
        metaDelegateByType(e, e.msg.sender, u, PROPOSITION_POWER(), deadline, v, r, s);
    
    if (type==0)
        metaDelegateByType@withrevert(e, e.msg.sender, u, PROPOSITION_POWER(), deadline, v, r, s) at init;
    else
        metaDelegateByType@withrevert(e, e.msg.sender, u, VOTING_POWER(), deadline, v, r, s) at init;
    assert lastReverted;
}


/**

    Verify that only delegate functions can change someone's delegate.
    An example for a parametric rule.

*/

rule votingDelegateChanges(address u, method f) {
    env e;
    calldataarg args;

    address _delegate = getVotingDelegate(u);

    f(e, args);

    address delegate_ = getVotingDelegate(u);

    // only these four function may change the delegate of an address
    assert delegate_ != _delegate =>
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

ghost mathint sumDelegatedVotingBalances {
    init_state axiom sumDelegatedVotingBalances == 0;
}

ghost mathint sumDelegatedPropositionBalances {
    init_state axiom sumDelegatedPropositionBalances == 0;
}

/**

    This hook updates the sumBalances ghost whenever any address balance is updated

*/
hook Sstore _balances[KEY address user].balance uint104 balance
    (uint104 old_balance) STORAGE {
        sumBalances = sumBalances - to_mathint(old_balance) + to_mathint(balance);
    }

hook Sstore _balances[KEY address user].delegatedVotingBalance uint72 delegatedVotingBalance
    (uint72 oldDelegatedVotingBalance) STORAGE {
        sumDelegatedVotingBalances = sumDelegatedVotingBalances 
        - to_mathint(oldDelegatedVotingBalance) 
        + to_mathint(delegatedVotingBalance);
    }

hook Sstore _balances[KEY address user].delegatedPropositionBalance uint72 delegatedPropositionBalance
    (uint72 oldDelegatedPropositionBalance) STORAGE {
        sumDelegatedPropositionBalances = sumDelegatedPropositionBalances
        - to_mathint(oldDelegatedPropositionBalance) 
        + to_mathint(delegatedPropositionBalance);
    }


/**

    Invariant: 
    sum of all addresses' balances should be always equal to the total supply of the token
    
*/
invariant totalSupplyEqualsBalances()
    sumBalances == totalSupply()
    filtered {
        f -> !f.isView
    }

invariant totalSupplyGETSumDelegatedVotingBalances()
    totalSupply() >= sumDelegatedVotingBalances * POWER_SCALE_FACTOR()
    { preserved with (env e) {
        requireInvariant isVotingDelegated(e.msg.sender);
        requireInvariant totalSupplyEqualsBalances();
    }}

invariant totalSupplyGETSumDelegatedPropositionBalances()
    totalSupply() >= sumDelegatedPropositionBalances * POWER_SCALE_FACTOR()
    { preserved with (env e) {
        requireInvariant isPropositionDelegated(e.msg.sender);
        requireInvariant totalSupplyEqualsBalances();
    }}

// rule totalSupplyGETSumDelegatedVotingBalances(method f) {
//   require totalSupply() <= totalSupplyGETSumDelegatedPropositionBalances();
//   calldataarg arg;
//   env e;
//   f(e, arg);
//   assert totalSupply() <= totalSupplyGETSumDelegatedPropositionBalances();
// }