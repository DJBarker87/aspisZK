fn NHU_transition_header_cut(public:SemanticPublic,log:&mut CarryLog)->Result<(u64,usize),PoolV1PairForestSemanticTerminalErrorV1>{
    let source = public.transition.live_snapshot;
    let after = public.transition.candidate_afterstate;
    if source.pool != public.pool
        || source.deployment_domain != public.deployment_domain
        || source.sequence != source.next_pair_index
        || source.next_pair_index >= POOL_V1_PAIR_CAPACITY
        || source.next_pair_index.checked_add(1) != Some(after.next_pair_index)
    {
        return Err(PoolV1PairForestSemanticTerminalErrorV1::InvalidAppendTransition);
    }
    let index = source.next_pair_index;
    let carry = carry_cut(index,log);

Ok((index,carry))
}
