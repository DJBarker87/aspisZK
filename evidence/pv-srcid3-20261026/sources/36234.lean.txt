import R1Z.PV_Src_ScalarFold
import R1Z.BuilderAdmissionCanonical

/-! Full wrapping-source reducer identity, not merely checked-add transport.
This is shared by the actual admission and owned external-layer extractions. -/
set_option autoImplicit false
namespace R1Z.PV_Src_ScalarReduce
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open AspisV8R17.RawReducer PV_Src_ScalarFold

def value (x : U64) : U32 :=
  let n := UScalar.cast .U32 (fold (fold x))
  if n ≥ 2147483647#u32 then U32.wrapping_sub n 2147483647#u32 else n

theorem value_raw (x : U64) : (value x).val = rawReduceU64 x.val := by
  rw [rawReduceU64,second_fold_cast_exact x.val x.bv.isLt]
  unfold value condSubP
  dsimp only [AspisV8R17.RawReducer.P]
  have hv := narrow_value x
  by_cases h : (UScalar.cast .U32 (fold (fold x))) ≥ 2147483647#u32
  · have hb : 2147483647 ≤ (UScalar.cast .U32 (fold (fold x))).val := by
      simpa only [UScalar.le_equiv,UScalar.ofNatCore_val_eq] using h
    rw [if_pos h,if_pos (by omega),u32_sub_small _ _ (by simpa using hb),hv]
    rfl
  · have hb : ¬2147483647 ≤ (UScalar.cast .U32 (fold (fold x))).val := by
      simpa only [UScalar.le_equiv,UScalar.ofNatCore_val_eq] using h
    rw [if_neg h,if_neg (by omega),hv]

theorem reference_eq (x : U64) :
    AspisBuilderPoseidonReference.aspis_core.field.M31.reduce_u62 x = ok (value x) := by
  simp only [AspisBuilderPoseidonReference.aspis_core.field.M31.reduce_u62,
    AspisBuilderPoseidonReference.aspis_core.field.reduce_u64,
    AspisBuilderPoseidonReference.aspis_core.field.P,lift,bind_tc_ok,value,fold,mask]
  split <;> rfl

theorem admission_eq (x : U64) :
    AspisBuilderAdmissionSource.aspis_core.field.reduce_u64 x = ok (value x) := by
  simp only [AspisBuilderAdmissionSource.aspis_core.field.reduce_u64,
    AspisBuilderAdmissionSource.aspis_core.field.P,lift,bind_tc_ok,value,fold,mask]
  split <;> rfl

theorem canonical (x : U64) : (value x).val < 2147483647 := by
  rw [value_raw]
  exact rawReduceU64_canonical x.val x.bv.isLt

theorem modulo (x : U64) : (value x).val = x.val % 2147483647 := by
  rw [value_raw]
  exact rawReduceU64_eq_mod_nat x.val x.bv.isLt

#print axioms value_raw
#print axioms reference_eq
#print axioms admission_eq
#print axioms canonical
#print axioms modulo
end R1Z.PV_Src_ScalarReduce
