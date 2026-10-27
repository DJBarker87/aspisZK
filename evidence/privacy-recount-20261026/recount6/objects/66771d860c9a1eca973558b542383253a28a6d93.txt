import R1Z.ProverRwP6BoundarySource
import R1Z.ProverCommitNativeOps47
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwP6BoundaryReduce
open Aeneas Aeneas.Std Result
theorem total (x : U64) :
    ∃ z, ProverRwP6BoundarySource.aspis_core.field.M31.reduce_u64 x = ok z := by
  obtain ⟨z, hz, _, _⟩ := AspisR1.ExtractedCurrentReducer.current_reduce_mod x
  have checked : AspisR1ProducerChecked47.field.reduce_u64 x = ok z := by
    rw [ProverCommitPrimitive47.reduce, hz]
  have release := ProverCommitRelease47.reduce x z checked
  refine ⟨z, ?_⟩
  exact (ProverRwSuccessCtReduce.reduce x).trans release
#print axioms total
end R1Z.ProverRwP6BoundaryReduce
