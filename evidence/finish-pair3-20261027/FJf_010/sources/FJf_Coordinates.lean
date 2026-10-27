import FJf_PointIndices
set_option autoImplicit false
namespace AspisR1.FJf_Coordinates
open Aeneas Aeneas.Std Result
/-- Small bounded index arithmetic, never a finite field evaluation. -/
theorem indices (t : Usize) (ht : t.val≤4) :
    (Usize.wrapping_sub 9#usize (Usize.wrapping_mul 2#usize t)).val=9-2*t.val ∧
    (Usize.wrapping_sub 8#usize (Usize.wrapping_mul 2#usize t)).val=8-2*t.val := by
  have size : 16≤UScalar.size .Usize := by
    rw [UScalar.size_def,UScalarTy.Usize_numBits_eq]
    rcases System.Platform.numBits_eq with h|h <;> simp [h]
  have prod : 2*t.val<UScalar.size .Usize := by omega
  have v2 : (2#usize).val=2 := by scalar_tac
  have v8 : (8#usize).val=8 := by scalar_tac
  have v9 : (9#usize).val=9 := by scalar_tac
  simp only [Usize.wrapping_sub_val_eq,Usize.wrapping_mul_val_eq,v2,v8,v9,
    Nat.mod_eq_of_lt prod]
  constructor
  · rw [show 9+(UScalar.size .Usize-2*t.val)=(9-2*t.val)+UScalar.size .Usize by omega,
      Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]
  · rw [show 8+(UScalar.size .Usize-2*t.val)=(8-2*t.val)+UScalar.size .Usize by omega,
      Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]
#print axioms indices
end AspisR1.FJf_Coordinates
