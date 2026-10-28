import R1Z.PV_RDB2C_PV_B2_C_251FieldTotal
import R1Z.PV_RDB2C_PV_B2_C_ConstructorEnvironment
set_option autoImplicit false
namespace PV_B2_D_RawHelpersTotal
open Aeneas Aeneas.Std Result PV_B2_251c1 PV_B2_C_ArrayTotal

theorem mask_bound (x : Usize) : (x &&& 3#usize).val < (4#usize).val := by
  change (x &&& 3#usize).bv.toNat < 4
  rw [UScalar.bv_and,BitVec.toNat_and]
  exact lt_of_le_of_lt (Nat.and_le_right) (by decide)

theorem tensor (f : Array (Array aspis_core.field.QM31 4#usize) 5#usize) (j : Usize) :
    Total (host_weights.tensor_raw f j) := by
  unfold host_weights.tensor_raw
  simp only [lift,bind_tc_ok,PV_B2_C_251FieldTotal.QM31_mul]
  repeat' first
    | exact ⟨_,rfl⟩
    | exact read _ _ (by decide)
    | exact read _ _ (mask_bound _)
    | apply PV_B2_C_ArrayTotal.bind
    | intro x

theorem factor (q : aspis_core.field.QM31) (r : Usize) (b : U32) :
    Total (host_weights.point_factor q r b) := by
  unfold host_weights.point_factor
  simp only [lift,bind_tc_ok,PV_B2_C_251FieldTotal.QM31_sub]
  split <;> exact ⟨_,rfl⟩

theorem point (points : Array aspis_core.field.QM31 10#usize) (r : Usize) :
    Total (host_weights.point_raw points r) := by
  unfold host_weights.point_raw
  simp only [PV_B2_C_251FieldTotal.QM31_mul]
  repeat' first
    | exact ⟨_,rfl⟩
    | exact read _ _ (by decide)
    | exact factor _ _ _
    | apply PV_B2_C_ArrayTotal.bind
    | intro x
#print axioms mask_bound
#print axioms tensor
#print axioms factor
#print axioms point
end PV_B2_D_RawHelpersTotal
