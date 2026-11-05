# NIX failed steps

NIX_K001: input compilation failure, KMX exact patch requires allocator_api in core crate. No solver verdict or native credit. L004 adds cfg_attr(kani,feature(allocator_api)) only in scratch; K002 is the changed-input attempt. No production source changed.

Transition task is already localized by NIH_K004/005, K021–030 and NIH_TRANSITION_DIAGNOSIS.md: problematic nested-field array inequality in reference, optimized Rust witness agrees with frozen source; explicit eight-word reference comparison passes arbitrary original prestate and failing control. Reuse NIH_TransitionWords.same_iff/different/guard. Tool encoding limit, no real source mismatch established. No unchanged replay authorized or needed.
