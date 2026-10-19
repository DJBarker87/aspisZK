import AspisR1BatchedWeightsExtraction.Funs
import ExtractedCurrentReducer

set_option autoImplicit false
namespace AspisR1.BatchedWeightsActualReducer
open Aeneas.Std

theorem generated_modulus_eq :
    AspisR1BatchedWeightsExtraction.aspis_core.field.P =
      AspisR1Qm31ArithmeticProbe.field.P := by
  unfold AspisR1BatchedWeightsExtraction.aspis_core.field.P
    AspisR1Qm31ArithmeticProbe.field.P
  rfl

/-- Exact equality of the newly emitted primitive and the retained proved
current-source reducer. No abstract reducer callback is introduced. -/
theorem generated_reduce_eq_current (x : U64) :
    AspisR1BatchedWeightsExtraction.aspis_core.field.reduce_u64 x =
      AspisR1Qm31ArithmeticProbe.field.reduce_u64 x := by
  unfold AspisR1BatchedWeightsExtraction.aspis_core.field.reduce_u64
    AspisR1Qm31ArithmeticProbe.field.reduce_u64
  rw [generated_modulus_eq]

theorem generated_wrapper_eq_current (x : U64) :
    AspisR1BatchedWeightsExtraction.aspis_core.field.M31.reduce_u64 x =
      AspisR1Qm31ArithmeticProbe.field.M31.reduce_u64 x := by
  simp only [AspisR1BatchedWeightsExtraction.aspis_core.field.M31.reduce_u64,
    AspisR1Qm31ArithmeticProbe.field.M31.reduce_u64, generated_reduce_eq_current]

/-- Every UInt64 input succeeds with the exact canonical residue, for the
actual newly emitted BatchedWeights field owner. -/
theorem generated_wrapper_mod (x : U64) :
    ∃ z : AspisR1BatchedWeightsExtraction.aspis_core.field.M31,
      AspisR1BatchedWeightsExtraction.aspis_core.field.M31.reduce_u64 x = .ok z ∧
      z.val = x.val % AspisV8R17.RawReducer.P ∧
      z.val < AspisV8R17.RawReducer.P := by
  rw [generated_wrapper_eq_current]
  exact AspisR1.ExtractedCurrentReducer.current_wrapper_mod x

#print axioms generated_modulus_eq
#print axioms generated_reduce_eq_current
#print axioms generated_wrapper_eq_current
#print axioms generated_wrapper_mod
end AspisR1.BatchedWeightsActualReducer
