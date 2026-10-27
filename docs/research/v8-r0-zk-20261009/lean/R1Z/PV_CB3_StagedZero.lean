import R1Z.PV_CB3_StagedPacking
set_option autoImplicit false
namespace R1Z.PV_CB3_StagedZero
open Aeneas Aeneas.Std
#print UScalar.eq_equiv_bv_eq
#print UScalar.eq_equiv

theorem neq_zero (v : BitVec 32) : ((⟨v⟩ : U32) != 0#u32) = decide (v ≠ 0#32) := by
  apply Bool.eq_iff_iff.mpr
  simp [bne,UScalar.eq_equiv_bv_eq,UScalar.zero_bv]
#print axioms neq_zero
end R1Z.PV_CB3_StagedZero
