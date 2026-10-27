import T2Nat_FinishCode
import RowFinish_Control
set_option autoImplicit false
noncomputable section
namespace AspisR1.T2Nat_FinishResult
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1Stage2.Stage2Finish
open T2Nat_Silent
attribute [local instance] Classical.propDecidable
variable {W : Type}

/-- The caller's actual error adapter, after the complete emitted parent.
This does not reduce a Result to its Boolean acceptance indicator. -/
def installed (ops : FinishOps W) (v : verifier.View) (p : verifier.Prepared)
    (a : verifier.Accumulator) : Silent (core.result.Result Unit VTop_Stages.verifier.Error) := do
  let r ← T2Nat_FinishCode.parent (Port4D_Round.native ops) v p a none
  call (Port3_QueryInstall.result (ok r))

theorem installed_erase (ops : FinishOps W) (v : verifier.View) (p : verifier.Prepared)
    (a : verifier.Accumulator) :
    erase (installed ops v p a) = Port4D_FinishInstall.finish ops v p a none := by
  simp only [installed,erase_bind,T2Nat_FinishCode.parent_erase,erase_call]
  unfold Port4D_FinishInstall.finish
  change _ = Port3_QueryInstall.result
    (Port3_NativeFinishBody.verifier.finish_relation (Port4D_Round.native ops) v p a none)
  cases Port3_NativeFinishBody.verifier.finish_relation (Port4D_Round.native ops) v p a none <;> rfl

theorem installed_effects {H : Type} (D : aspis_core.digest.Digest32 H) (hash : H)
    (ops : FinishOps W) (v : verifier.View) (p : verifier.Prepared)
    (a : verifier.Accumulator) (before : CheckpointBytes5Effect.Log) :
    CheckpointBytes5Effect.run D hash (code (installed ops v p a)) before =
      (do let r ← Port4D_FinishInstall.finish ops v p a none; ok (r,before)) := by
  rw [ordered_log,installed_erase]

/-- On the actual successful call there are no new oracle events; the entire
incoming ordered log, including rejected earlier prefixes, is retained. -/
theorem accepted_effects {H : Type} (D : aspis_core.digest.Digest32 H) (hash : H)
    (ops : FinishOps W) (v : verifier.View) (p : verifier.Prepared)
    (a : verifier.Accumulator)
    (accepted : Port4D_FinishInstall.finish ops v p a none = ok (.Ok ()))
    (before : CheckpointBytes5Effect.Log) :
    CheckpointBytes5Effect.run D hash (code (installed ops v p a)) before =
      ok (.Ok (),before) := by
  rw [installed_effects,accepted]
  rfl

/-- Ordered errors are the source's Relation and Query errors, at the exact
comparison priority. Primitive-error/fail/div cases remain in installed_erase.
The total leaf premises are the existing named arithmetic owner obligations. -/
theorem full_result (ops : FinishOps W) (v : verifier.View) (p : verifier.Prepared)
    (a : verifier.Accumulator) (alpha0 alpha1 : E)
    (r0 : RowFinish_Control.RoundValues ops v.round0 alpha0 p.claim)
    (r1 : RowFinish_Control.RoundValues ops v.round1 alpha1 r0.value)
    (weights : W) (alphas : Slice E) (pair dot : E)
    (s2 : p.variant = .S2)
    (ha0 : Array.index_usize p.alpha 0#usize = ok alpha0)
    (ha1 : Array.index_usize p.alpha 1#usize = ok alpha1)
    (hw : ops.newWeights p.variant p.semantic_alpha p.z = ok (.Ok weights))
    (has : core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice E)) p.alpha { «end» := 2#usize } = ok alphas)
    (hp : ops.pair weights alphas v.final_message p.kappa = ok (.Ok pair))
    (hd : ops.dot v.final_message a.weights.deref = ok (.Ok dot)) :
    Port4D_FinishInstall.finish ops v p a none =
      ok (if r0.lhs ≠ r0.rhs then .Err (Port3_CheckpointInstall.error verifier.Error.Relation)
        else if r1.lhs ≠ r1.rhs then .Err (Port3_CheckpointInstall.error verifier.Error.Relation)
        else if pair ≠ r1.value then .Err (Port3_CheckpointInstall.error verifier.Error.Relation)
        else if a.next ≠ 22#usize then .Err (Port3_CheckpointInstall.error verifier.Error.Query)
        else if dot ≠ a.rhs then .Err (Port3_CheckpointInstall.error verifier.Error.Query) else .Ok ()) := by
  classical
  have normal := RowFinish_Control.parent_value ops v p a alpha0 alpha1 r0 r1
    weights alphas pair dot s2 ha0 ha1 hw has hp hd
  change Port3_QueryInstall.result
    (Port3_NativeFinishBody.verifier.finish_relation (Port4D_Round.native ops) v p a none) = _
  rw [normal]
  by_cases e0 : r0.lhs = r0.rhs <;> by_cases e1 : r1.lhs = r1.rhs <;>
    by_cases ep : pair = r1.value <;> by_cases en : a.next = 22#usize <;>
    by_cases ed : dot = a.rhs
  all_goals simp [Port3_QueryInstall.result,e0,e1,ep,en,ed]

#print axioms installed_erase
#print axioms installed_effects
#print axioms accepted_effects
#print axioms full_result
end AspisR1.T2Nat_FinishResult
end
