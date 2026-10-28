import S8Kani2MutableSource
import BatchedWeightsActualReducer
set_option autoImplicit false
namespace AspisR1.NCI_PendingReducer
open Aeneas Aeneas.Std Result

theorem primitive_eq (x : U64) :
    S8Kani2MutableExtraction.aspis_core.field.reduce_u64 x =
      AspisR1BatchedWeightsExtraction.aspis_core.field.reduce_u64 x := by
  unfold S8Kani2MutableExtraction.aspis_core.field.reduce_u64
    AspisR1BatchedWeightsExtraction.aspis_core.field.reduce_u64
    S8Kani2MutableExtraction.aspis_core.field.P
    AspisR1BatchedWeightsExtraction.aspis_core.field.P
  rfl

theorem reducer_ok (x : U64) : ∃ z,
    S8Kani2MutableExtraction.aspis_core.field.M31.reduce_u64 x = ok z ∧
    z.val=x.val%2147483647 ∧ z.val<2147483647 := by
  have eq : S8Kani2MutableExtraction.aspis_core.field.M31.reduce_u64 x =
      AspisR1BatchedWeightsExtraction.aspis_core.field.M31.reduce_u64 x := by
    simp only [S8Kani2MutableExtraction.aspis_core.field.M31.reduce_u64,
      AspisR1BatchedWeightsExtraction.aspis_core.field.M31.reduce_u64,primitive_eq]
  rw [eq]
  exact BatchedWeightsActualReducer.generated_wrapper_mod x
#print axioms primitive_eq
#print axioms reducer_ok
end AspisR1.NCI_PendingReducer
