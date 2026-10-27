import Port4D_FinishInstall

set_option autoImplicit false
noncomputable section
namespace AspisR1.RowFinish_Control
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1Stage2.Stage2Finish
attribute [local instance] Classical.propDecidable
variable {W : Type}

/-- Total primitive evaluations at one round's exact operands. These are
leaf source/backend obligations, stronger than one-way success interpretation.
No comparison outcome or parent success is supplied. -/
structure RoundValues (ops : FinishOps W) (bytes : Slice U8) (alpha claim : E) where
  c0 : E
  c4 : E
  lhs : E
  quarter : M
  rhs : E
  value : E
  field0 : ops.field bytes 0#usize = ok c0
  field4 : ops.field bytes 4#usize = ok c4
  add : ops.add c0 c4 = ok lhs
  quarter_run : ops.quarter = ok quarter
  multiply : ops.mulM claim quarter = ok rhs
  evaluate : ops.polynomial bytes alpha = ok value

/-- Complete round, including a failed comparison. Release tracing is silent;
the source wrapping index arithmetic remains the current source operation. -/
theorem round_value (ops : FinishOps W) (bytes : Slice U8) (alpha claim : E)
    (r : Usize) (b : RoundValues ops bytes alpha claim) :
    Port4D_Round.round (Port3_FinishStage.release ops) bytes alpha claim r =
      ok (if b.lhs = b.rhs then .Ok b.value else .Err verifier.Error.Relation) := by
  by_cases same : b.lhs = b.rhs
  all_goals simp [Port4D_Round.round,Port3_FinishStage.release,Port3_FinishStage.ne,
    b.field0,b.field4,b.add,b.quarter_run,b.multiply,b.evaluate,same,lift]

/-- Exact S2 parent result. Totality is required only for primitive evaluations
on the supplied operands; no whole finish law is a premise. Both rejection
kinds and source comparison order are retained. -/
theorem parent_value (ops : FinishOps W) (v : verifier.View) (p : verifier.Prepared)
    (a : verifier.Accumulator) (alpha0 alpha1 : E)
    (r0 : RoundValues ops v.round0 alpha0 p.claim)
    (r1 : RoundValues ops v.round1 alpha1 r0.value)
    (weights : W) (alphas : Slice E) (pair dot : E)
    (s2 : p.variant = .S2)
    (ha0 : Array.index_usize p.alpha 0#usize = ok alpha0)
    (ha1 : Array.index_usize p.alpha 1#usize = ok alpha1)
    (hw : ops.newWeights p.variant p.semantic_alpha p.z = ok (.Ok weights))
    (has : core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice E)) p.alpha { «end» := 2#usize } = ok alphas)
    (hp : ops.pair weights alphas v.final_message p.kappa = ok (.Ok pair))
    (hd : ops.dot v.final_message a.weights.deref = ok (.Ok dot)) :
    Port3_NativeFinishBody.verifier.finish_relation (Port4D_Round.native ops) v p a none =
      ok (if r0.lhs ≠ r0.rhs then .Err verifier.Error.Relation
        else if r1.lhs ≠ r1.rhs then .Err verifier.Error.Relation
        else if pair ≠ r1.value then .Err verifier.Error.Relation
        else if a.next ≠ 22#usize then .Err verifier.Error.Query
        else if dot ≠ a.rhs then .Err verifier.Error.Query else .Ok ()) := by
  have h0 := round_value ops v.round0 alpha0 p.claim 0#usize r0
  have h1 := round_value ops v.round1 alpha1 r0.value 1#usize r1
  dsimp only [Port3_FinishStage.release] at h0 h1
  simp only [s2] at hw
  simp only [core.array.Array.index] at has
  unfold Port3_NativeFinishBody.verifier.finish_relation Port4D_Round.native Port3_FinishStage.native
  by_cases e0 : r0.lhs = r0.rhs <;> by_cases e1 : r1.lhs = r1.rhs <;>
    by_cases ep : pair = r1.value <;> by_cases en : a.next = 22#usize <;>
    by_cases ed : dot = a.rhs
  all_goals simp [ha0,ha1,h0,h1,hw,has,hp,hd,s2,Port3_FinishStage.release,
    Port3_FinishStage.folds,Port3_FinishStage.ne,Port3_QueryStage.mark,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame.from,e0,e1,ep,en,ed]

#print axioms round_value
#print axioms parent_value
end AspisR1.RowFinish_Control
end
