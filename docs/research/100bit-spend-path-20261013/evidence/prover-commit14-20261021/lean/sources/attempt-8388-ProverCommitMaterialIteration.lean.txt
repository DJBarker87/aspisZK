import R1Z.ProverCommitMaterialRecursion
/-! Exact one-iteration equations with arbitrary owned vector prefixes.
The scalar callees stay named; no sixteen-try recurrence is normalized. -/
set_option autoImplicit false
namespace R1Z.ProverCommitMaterialIteration
open Aeneas Aeneas.Std Result AspisR1ProverMaterial14
open R1Z.ProverCommitMaterialRecursion (Hash State Values QValues)

theorem m31_iteration (hash : Hash) (domain : Slice U8) (state : State) (values : Values) :
    prover_commit_reference.collect_m31_owned hash domain state 1#usize values = (do
      let (sample, after) ← prover_commit_reference.limb_caller hash domain state
      match sample with
      | .Err error => ok (.Err error, values, after)
      | .Ok value =>
        let fresh ← alloc.vec.Vec.push values value
        ok (.Ok (), fresh, after)) := by
  rw [ProverCommitMaterialRecursion.extracted_finite hash domain 1 1#usize values state (by decide)]
  rfl

theorem qm31_iteration (hash : Hash) (domain : Slice U8) (state : State) (values : QValues) :
    prover_commit_reference.collect_qm31_owned hash domain state 1#usize values = (do
      let (sample, after) ← prover_commit_reference.qm31_caller hash domain state
      match sample with
      | .Err error => ok (.Err error, values, after)
      | .Ok value =>
        let fresh ← alloc.vec.Vec.push values value
        ok (.Ok (), fresh, after)) := by
  rw [ProverCommitMaterialRecursion.qm_extracted_finite hash domain 1 1#usize values state (by decide)]
  rfl

#print axioms m31_iteration
#print axioms qm31_iteration
end R1Z.ProverCommitMaterialIteration
