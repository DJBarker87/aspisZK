fn NHU_transition_step_cut(public:SemanticPublic,carry:usize,level:usize)->Result<usize,PoolV1PairForestSemanticTerminalErrorV1>{let source=public.transition.live_snapshot;let after=public.transition.candidate_afterstate;let index=source.next_pair_index;let mut iter=level..20;if let Some(level)=iter.next(){
        if level == carry && carry < 20 {
            return Ok(iter.start);
        }
        let expected = if level < carry || ((index >> level) & 1) == 0 {
            empty_root(level)
        } else {
            source.frontier[level]
        };
        if after.next_frontier[level] != expected {
            return Err(PoolV1PairForestSemanticTerminalErrorV1::InvalidAppendTransition);
        }
}
Ok(iter.start)
}
