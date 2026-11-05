# NIX failed steps

NIX_K001: input compilation failure, KMX exact patch requires allocator_api in core crate. No solver verdict or native credit. L004 adds cfg_attr(kani,feature(allocator_api)) only in scratch; K002 is the changed-input attempt. No production source changed.

Transition task is already localized by NIH_K004/005, K021–030 and NIH_TRANSITION_DIAGNOSIS.md: problematic nested-field array inequality in reference, optimized Rust witness agrees with frozen source; explicit eight-word reference comparison passes arbitrary original prestate and failing control. Reuse NIH_TransitionWords.same_iff/different/guard. Tool encoding limit, no real source mismatch established. No unchanged replay authorized or needed.

NIX_L005 mixed-name inspection fails several #prints; independent printed definitions are retained, no object credit. NIX_L006 scalar_tac alone does not normalize literal projections; L007 broad norm_num hits the recursion limit. L009 changes shape: literal rfl first, then scalar preprocessing and explicit guard splits; passes. No recursion/heartbeat setting is raised.

NIX_L010 reaches the exact parser reply but over-injects an equality already simplified to a conjunction; L015 uses its first projection and passes. L011 aggregate prefix draft cannot split a leading let; L016 deep dsimp reaches the recursion limit. A head-only change/rw proof is pending. Failed drafts and printed sorryAx placeholders are excluded from admission.

NIX_L012 stops before a scope on own missing RPv_F3M_CircleSourceCall import; L017 removes the guessed import and inventories actual environment declarations. The attempted L014 while the previous owned client was draining is refused by the owned exclusivity guard before admission/submission; its first actual submission occurs after that client completes. No concurrent scope is launched.

NIX_K004–009 are failed compilation preflights of the same wrong reserve-stub generic arity (queue error retained; never credit). The owned queue is stopped; later queues stop on compile errors as well as timeout/memory. L014 supplies the generic T,A signature. K012 fails a builtin memcmp unwinding assertion, not a semantic frame counterexample; L021 splits frame comparisons into two scalar assertions and preserves the actual c1 comparison with its known finite 8-byte bound. Neither failure is classified as a source bug.
