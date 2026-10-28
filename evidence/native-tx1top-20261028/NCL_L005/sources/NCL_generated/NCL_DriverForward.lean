import NCL_DriverCuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.NCL_DriverForward
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
attribute [local irreducible] verifier.candidate.prepare

/-- Replay the emitted outer driver on the SAME proof/public/hash and the
same carriers in source order. All observations are local child statements;
none is a second whole-driver acceptance premise. -/
theorem source (ops : Ops) {H : Type} (D : aspis_core.digest.Digest32 H)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (hash : H) (saved : alloc.vec.Vec U8)
    (start : compact.OFF_FOLDED_ROOT ops = ok 7751#usize)
    (finish : compact.OFF_ROUND1 ops = ok 7783#usize)
    (c : NCL_DriverCuts.Cuts ops D semantic pub proof hash saved) :
    verifier.candidate.tx1 ops D semantic pub proof 10#usize hash none = ok (.Ok saved) := by
  simp only [verifier.candidate.tx1,compact.SPLIT,bne_self_eq_false,Bool.false_eq_true,
    if_false,verifier.candidate.parse_shape,verifier.candidate.canonical_scan,
    c.shape,c.scan,c.zero_call,c.prepare,c.initial_call,start,finish,c.root_range,c.root_copy,
    c.batch,c.geometry_call,c.pending_call,c.query,c.flush,c.checkpoint,
    verifier.mark,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,
    verifier.Accumulator.new,verifier.candidate.batch_merkle,verifier.QueryGeometry.for_range,
    verifier.BatchedWeights.new,verifier.candidate.query_loop,verifier.BatchedWeights.finish,
    verifier.checkpoint,core.result.Result.unwrap,alloc.vec.Vec.deref_mut,alloc.vec.Vec.deref]
#print axioms source
end AspisR1.NCL_DriverForward
end
