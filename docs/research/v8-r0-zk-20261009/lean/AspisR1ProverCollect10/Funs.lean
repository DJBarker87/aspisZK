import AspisR1ProverStep8.Funs
/-! Shared extraction port: all five dependencies of this generated function
are byte-identical definitions already adopted in ProverStep8. Reuse their
namespace and nominal types; the new function body is verbatim Aeneas output.
See prover-commit10-20261021/extraction/shared-declarations.json. -/
open Aeneas Aeneas.Std Result ControlFlow Error
namespace AspisR1ProverStep8
def prover_commit_reference.collect_m31_owned
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (domain : Slice Std.U8) (state : prover_commit_reference.State)
  (remaining : Std.Usize) (values : alloc.vec.Vec aspis_core.field.M31) :
  Result ((core.result.Result Unit state_only_hiding.StateOnlyMaskBuildError)
    × (alloc.vec.Vec aspis_core.field.M31) × prover_commit_reference.State)
  := do
  if remaining = 0#usize
  then ok (core.result.Result.Ok (), values, state)
  else
    let (sample, state1) ←
      prover_commit_reference.limb_caller hash domain state
    match sample with
    | core.result.Result.Ok value =>
      let values1 ← alloc.vec.Vec.push values value
      let i ← lift (Std.Usize.wrapping_sub remaining 1#usize)
      prover_commit_reference.collect_m31_owned hash domain state1 i values1
    | core.result.Result.Err error =>
      ok (core.result.Result.Err error, values, state1)
partial_fixpoint
end AspisR1ProverStep8
