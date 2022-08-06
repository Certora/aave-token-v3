import "./setup.spec"

methods {
    delegateByType(address delegatee, uint8 delegationType)
    getDelegatedPower(address user, uint8 delegationType) returns (uint256) envfree
    getDelegateeByType(address delegator, uint8 delegationType) returns (address) envfree
}

/*
    @Invariant

    @Description:
        A user's total power equals to 
            its delegated power if the user is delegating, or 
            its delegated power plus its own token balance if the user is not delegating

*/
invariant power_equations(address user)
    getDelegatingVoting(user) => getPowerCurrent(user, VOTING_POWER()) ==  getDelegatedPower(user, VOTING_POWER())
    &&
    !getDelegatingVoting(user) => getPowerCurrent(user, VOTING_POWER()) == balanceOf(user) + getDelegatedPower(user, VOTING_POWER())
    &&
    getDelegatingProposition(user) => getPowerCurrent(user, PROPOSITION_POWER()) == getDelegatedPower(user, PROPOSITION_POWER())
    &&
    !getDelegatingProposition(user) => getPowerCurrent(user, PROPOSITION_POWER()) == balanceOf(user) + getDelegatedPower(user, PROPOSITION_POWER())

/*
    @Rule

    @Description:
        calling 
            delegate
            delegateByType
            metaDelegate
            metaDelegateByType 
        functions should have the same effect on involved accounts' 
            voting power
            proposition power
            delegate
*/
rule equivalence_of_delegate_functions(address other) {
    env e;
    // delegate not to self or to zero
    address self = e.msg.sender;
    require other != self && other != 0;
    uint256 otherDelegatedBalance = getDelegatedVotingBalance(other);
    // avoid unrealistic delegated balance
    require(otherDelegatedBalance < MAX_DELEGATED_BALANCE());
    // make sure the sender doesn't already delegate to other
    address delegateBefore = getVotingDelegate(self);
    require delegateBefore != other;

    storage init = lastStorage;

    delegate(e, other);
    uint256 _myVotingPower = getPowerCurrent(self, VOTING_POWER());
    uint256 _myPropositionPower = getPowerCurrent(self, PROPOSITION_POWER());
    uint256 _otherVotingPower = getPowerCurrent(other, VOTING_POWER());
    uint256 _otherPropositionPower = getPowerCurrent(other, PROPOSITION_POWER());
    address _myVotingDelegate = getVotingDelegate(self);
    address _myPropositionDelegate = getPropositionDelegate(self);

    delegateByType(e, other, VOTING_POWER()) at init;
    uint256 myVotingPower_ = getPowerCurrent(self, VOTING_POWER());
    uint256 otherVotingPower_ = getPowerCurrent(other, VOTING_POWER());
    address myVotingDelegate_ = getVotingDelegate(self);

    delegateByType(e, other, PROPOSITION_POWER()) at init;
    uint256 myPropositionPower_ = getPowerCurrent(self, PROPOSITION_POWER());
    uint256 otherPropositionPower_ = getPowerCurrent(other, PROPOSITION_POWER());
    address myPropositionDelegate_ = getPropositionDelegate(self);

    uint256 deadline; 
    uint8 v; 
    bytes32 r; 
    bytes32 s;
    metaDelegate(e, self, other, deadline, v, r, s) at init;
    uint256 myVotingPower_metaDelegate = getPowerCurrent(self, VOTING_POWER());
    uint256 myPropositionPower_metaDelegate = getPowerCurrent(self, PROPOSITION_POWER());
    uint256 otherVotingPower_metaDelegate = getPowerCurrent(other, VOTING_POWER());
    uint256 otherPropositionPower_metaDelegate = getPowerCurrent(other, PROPOSITION_POWER());
    address myVotingDelegate_metaDelegate = getVotingDelegate(self);
    address myPropositionDelegate_metaDelegate = getPropositionDelegate(self);

    metaDelegateByType(e, self, other, VOTING_POWER(), deadline, v, r, s) at init;
    uint256 myVotingPower_metaDelegateByType = getPowerCurrent(self, VOTING_POWER());
    uint256 otherVotingPower_metaDelegateByType = getPowerCurrent(other, VOTING_POWER());
    address myVotingDelegate_metaDelegateByType = getVotingDelegate(self);

    metaDelegateByType(e, self, other, PROPOSITION_POWER(), deadline, v, r, s) at init;
    uint256 myPropositionPower_metaDelegateByType = getPowerCurrent(self, PROPOSITION_POWER());
    uint256 otherPropositionPower_metaDelegateByType = getPowerCurrent(other, PROPOSITION_POWER());
    address myPropositionDelegate_metaDelegateByType = getPropositionDelegate(self);

    assert _myVotingPower == myVotingPower_;
    assert _myPropositionPower == myPropositionPower_;
    assert _myVotingDelegate == myVotingDelegate_;
    assert _myPropositionDelegate == myPropositionDelegate_;
    assert _otherVotingPower == otherVotingPower_;
    assert _otherPropositionPower == otherPropositionPower_;

    assert _myVotingPower == myVotingPower_metaDelegate;
    assert _myPropositionPower == myPropositionPower_metaDelegate;
    assert _myVotingDelegate == myVotingDelegate_metaDelegate;
    assert _myPropositionDelegate == myPropositionDelegate_metaDelegate;
    assert _otherVotingPower == otherVotingPower_metaDelegate;
    assert _otherPropositionPower == otherPropositionPower_metaDelegate; 
    
    assert _myVotingPower == myVotingPower_metaDelegateByType;
    assert _myPropositionPower == myPropositionPower_metaDelegateByType;
    assert _myVotingDelegate == myVotingDelegate_metaDelegateByType;
    assert _myPropositionDelegate == myPropositionDelegate_metaDelegateByType;
    assert _otherVotingPower == otherVotingPower_metaDelegateByType;
    assert _otherPropositionPower == otherPropositionPower_metaDelegateByType;
}

/*
    @Rule

    @Description:
        delegate to self and delegate to zero address are equivalent
*/
rule equivalence_of_self_and_zero_addresses(address other) {
    env e;
    address self = e.msg.sender;
    require self != other;

    storage init = lastStorage;

    delegate(e, self); // delegate to self

    address _myVotingDelegate = getVotingDelegate(self);
    address _myPropositionDelegate = getPropositionDelegate(self);
    uint256 _myVotingPower = getPowerCurrent(self, VOTING_POWER());
    uint256 _myPropositionPower = getPowerCurrent(self, PROPOSITION_POWER());

    address _otherVotingDelegate = getVotingDelegate(other);
    address _otherPropositionDelegate = getPropositionDelegate(other);
    uint256 _otherVotingPower = getPowerCurrent(other, VOTING_POWER());
    uint256 _otherPropositionPower = getPowerCurrent(other, PROPOSITION_POWER());

    delegate(e, 0) at init; // delegate to 0

    address myVotingDelegate_ = getVotingDelegate(self);
    address myPropositionDelegate_ = getPropositionDelegate(self);
    uint256 myVotingPower_ = getPowerCurrent(self, VOTING_POWER());
    uint256 myPropositionPower_ = getPowerCurrent(self, PROPOSITION_POWER());

    address otherVotingDelegate_ = getVotingDelegate(other);
    address otherPropositionDelegate_ = getPropositionDelegate(other);
    uint256 otherVotingPower_ = getPowerCurrent(other, VOTING_POWER());
    uint256 otherPropositionPower_ = getPowerCurrent(other, PROPOSITION_POWER());

    assert _myVotingDelegate == myVotingDelegate_;
    assert _myPropositionDelegate == myPropositionDelegate_;
    assert _myVotingPower == myVotingPower_;
    assert _myPropositionPower == myPropositionPower_;
    
    assert _otherVotingDelegate == otherVotingDelegate_;
    assert _otherPropositionDelegate == otherPropositionDelegate_;
    assert _otherVotingPower == otherVotingPower_;
    assert _otherPropositionPower == otherPropositionPower_;
}


/*
    @Rule

    @Description:
        If a user has not delegated to anyone and now delegates to self,
        it should affect nothing.
*/
rule self_delegation_affects_nothing(address other) {
    env e;
    address self = e.msg.sender;
    require self != other;

    address _myVotingDelegate = getVotingDelegate(self);
    address _myPropositionDelegate = getPropositionDelegate(self);
    uint256 _myVotingPower = getPowerCurrent(self, VOTING_POWER());
    uint256 _myPropositionPower = getPowerCurrent(self, PROPOSITION_POWER());

    require _myVotingDelegate == 0 && _myPropositionDelegate == 0; // not delegating to anyone

    address _otherVotingDelegate = getVotingDelegate(other);
    address _otherPropositionDelegate = getPropositionDelegate(other);
    uint256 _otherVotingPower = getPowerCurrent(other, VOTING_POWER());
    uint256 _otherPropositionPower = getPowerCurrent(other, PROPOSITION_POWER());

    delegate(e, self); // delegate to self

    address myVotingDelegate_ = getVotingDelegate(self);
    address myPropositionDelegate_ = getPropositionDelegate(self);
    uint256 myVotingPower_ = getPowerCurrent(self, VOTING_POWER());
    uint256 myPropositionPower_ = getPowerCurrent(self, PROPOSITION_POWER());

    address otherVotingDelegate_ = getVotingDelegate(other);
    address otherPropositionDelegate_ = getPropositionDelegate(other);
    uint256 otherVotingPower_ = getPowerCurrent(other, VOTING_POWER());
    uint256 otherPropositionPower_ = getPowerCurrent(other, PROPOSITION_POWER());

    assert _myVotingDelegate == myVotingDelegate_;
    assert _myPropositionDelegate == myPropositionDelegate_;
    assert _myVotingPower == myVotingPower_;
    assert _myPropositionPower == myPropositionPower_;
    
    assert _otherVotingDelegate == otherVotingDelegate_;
    assert _otherPropositionDelegate == otherPropositionDelegate_;
    assert _otherVotingPower == otherVotingPower_;
    assert _otherPropositionPower == otherPropositionPower_;
}

/*
    @Rule

    @Description:
        If a user has delegated to someone and now delegate to someone else,
        it should only affect delegatees' power, while not affecting self and other's power.
*/
rule changing_delegatee_affects_delegatees_only(address newDelegatee, uint8 delegationType, address other) {
    env e;
    address self = e.msg.sender;
    require self != other && self != newDelegatee && newDelegatee != other && newDelegatee != 0;
    require delegationType == VOTING_POWER() || delegationType == PROPOSITION_POWER();
    if (delegationType == VOTING_POWER()) {
        require getDelegatingVoting(self);
    } else {
        require getDelegatingProposition(self);
    }
    address delegatee = getDelegateeByType(self, delegationType);
    require delegatee != other && delegatee != self && delegatee != newDelegatee && delegatee != 0;

    uint256 selfBalance = balanceOf(self);
    uint256 _selfPower = getPowerCurrent(self, delegationType);
    uint256 _delegateePower = getPowerCurrent(delegatee, delegationType);
    uint256 _newDelegateePower = getPowerCurrent(newDelegatee, delegationType);
    uint256 _otherPower = getPowerCurrent(other, delegationType);

    require selfBalance < MAX_DELEGATED_BALANCE();
    require _selfPower < MAX_DELEGATED_BALANCE();
    require _delegateePower < MAX_DELEGATED_BALANCE();
    require _newDelegateePower < MAX_DELEGATED_BALANCE();
    require _selfPower >= selfBalance;

    delegateByType(e, newDelegatee, delegationType); // change delegate

    uint256 selfPower_ = getPowerCurrent(self, delegationType);
    uint256 delegateePower_ = getPowerCurrent(delegatee, delegationType);
    uint256 newDelegateePower_ = getPowerCurrent(newDelegatee, delegationType);
    uint256 otherPower_ = getPowerCurrent(other, delegationType);

    assert getDelegateeByType(self, delegationType) == newDelegatee;
    assert _selfPower == selfPower_; // selfPower does not change
    assert _delegateePower - normalize(selfBalance) == delegateePower_; // delegateePower decreased by selfBalance
    assert _newDelegateePower + normalize(selfBalance) == newDelegateePower_; // newDelegateePower increased by selfBalance
    assert _otherPower == otherPower_; // otherPower does not change
}

/*
    @Rule

    @Description:
        If a user delegates to the same address more than once, the subsequent delegations do not change anything
*/
rule idempotency_of_delegation(address delegatee) {
    env e;
    address self = e.msg.sender;

    delegate(e, delegatee); // first delegation
    uint256 _myVotingPower = getPowerCurrent(self, VOTING_POWER());
    uint256 _myPropositionPower = getPowerCurrent(self, PROPOSITION_POWER());
    uint256 _delegateeVotingPower = getPowerCurrent(delegatee, VOTING_POWER());
    uint256 _delegateePropositionPower = getPowerCurrent(delegatee, PROPOSITION_POWER());
    address _myVotingDelegate = getVotingDelegate(self);
    address _myPropositionDelegate = getPropositionDelegate(self);

    delegate(e, delegatee); // second delegation
    uint256 myVotingPower_ = getPowerCurrent(self, VOTING_POWER());
    uint256 myPropositionPower_ = getPowerCurrent(self, PROPOSITION_POWER());
    uint256 delegateeVotingPower_ = getPowerCurrent(delegatee, VOTING_POWER());
    uint256 delegateePropositionPower_ = getPowerCurrent(delegatee, PROPOSITION_POWER());
    address myVotingDelegate_ = getVotingDelegate(self);
    address myPropositionDelegate_ = getPropositionDelegate(self);

    assert _myVotingDelegate == myVotingDelegate_;
    assert _myPropositionDelegate == myPropositionDelegate_;
    assert _myVotingPower == myVotingPower_;
    assert _myPropositionPower == myPropositionPower_;
    assert _delegateeVotingPower == delegateeVotingPower_;
    assert _delegateePropositionPower == delegateePropositionPower_;
}

/*
    @Rule

    @Description:
        only transferring functions affect user's token balance
*/
rule only_transfer_affect_balance(address user, method f) {

    uint256 _balance = balanceOf(user);

    env e;
    calldataarg args;
    f(e, args);

    uint256 balance_ = balanceOf(user);

    assert _balance != balance_ =>
        f.selector == transfer(address, uint256).selector || 
        f.selector == transferFrom(address, address, uint256).selector;
}