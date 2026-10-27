import RowFinish_Control
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGo_TX2_FinishPrefixTools
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1Stage2.Stage2Finish

def remaining {W : Type} (ops : Port3_NativeFinishBody.Ops W)
    (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
    (weights : W) (alphas : Slice E) (lastClaim : E) :
    Result (core.result.Result Unit verifier.Error) := do
  let r3 ← ops.op2 weights alphas v.final_message p.kappa
  let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
  match cf3 with
  | .Continue pair =>
    ops.op0 16#u16 0#usize pair
    ops.op0 16#u16 1#usize lastClaim
    let different ← ops.ne pair lastClaim
    if different then ok (.Err verifier.Error.Relation)
    else
      ops.op1 none verifier.Phase.Relation
      let r4 ← ops.op4 v.final_message a.weights.deref
      let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r4
      match cf4 with
      | .Continue dot =>
        ops.op0 17#u16 0#usize dot
        ops.op0 17#u16 1#usize a.rhs
        if a.next != 22#usize then ok (.Err verifier.Error.Query)
        else
          let different ← ops.ne dot a.rhs
          if different then ok (.Err verifier.Error.Query)
          else
            ops.op1 none verifier.Phase.Final
            ok (.Ok ())
      | .Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          Unit (core.convert.FromSame verifier.Error) residual
  | .Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Unit (core.convert.FromSame verifier.Error) residual

/-- Exact prefix elimination; both remaining gates and all error carriers stay
in the returned computation. No parent acceptance is a premise. -/
theorem source {W : Type} (ops : Port3_NativeFinishBody.Ops W)
    (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
    (alpha0 alpha1 claim0 claim1 : E) (weights : W) (alphas : Slice E)
    (read0 : Array.index_usize p.alpha 0#usize=ok alpha0)
    (round0 : ops.op5 v.round0 alpha0 p.claim 0#usize=ok (.Ok claim0))
    (folds : ops.op6 p.variant=ok 2#usize)
    (read1 : Array.index_usize p.alpha 1#usize=ok alpha1)
    (round1 : ops.op5 v.round1 alpha1 claim0 1#usize=ok (.Ok claim1))
    (newWeights : ops.op3 p.variant p.semantic_alpha p.z=ok (.Ok weights))
    (readAlphas : core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice E)) p.alpha {«end»:=2#usize}=ok alphas) :
    Port3_NativeFinishBody.verifier.finish_relation ops v p a none=
      remaining ops v p a weights alphas claim1 := by
  unfold Port3_NativeFinishBody.verifier.finish_relation
  rw [read0,bind_tc_ok,round0,bind_tc_ok]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,Aeneas.Std.uncurry]
  rw [folds,bind_tc_ok,if_pos rfl,read1,bind_tc_ok,round1,bind_tc_ok]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,Aeneas.Std.uncurry]
  rw [newWeights,bind_tc_ok]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,Aeneas.Std.uncurry]
  rw [readAlphas,bind_tc_ok]
  rfl
#print axioms source
end AspisR1.JGo_TX2_FinishPrefixTools
end
