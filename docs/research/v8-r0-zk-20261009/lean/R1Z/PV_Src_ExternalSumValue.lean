import R1Z.PV_Src_ExternalSumCells

/-! No U64 overflow occurs in a column sum of four arbitrary U32 words. -/
set_option autoImplicit false
namespace R1Z.PV_Src_ExternalSumValue
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_Src_ExternalSumStep

theorem value (s : State) (col : Usize) :
    (cell s col).val = s.val[col.val]!.val+s.val[col.val+4]!.val+
      s.val[col.val+8]!.val+s.val[col.val+12]!.val := by
  exact sum4_val _ _ _ _

theorem bound (s : State) (col : Usize) : (cell s col).val < 17179869184 := by
  rw [value]
  have := u32lt s.val[col.val]!
  have := u32lt s.val[col.val+4]!
  have := u32lt s.val[col.val+8]!
  have := u32lt s.val[col.val+12]!
  omega

theorem lift (s : State) (col : Usize) {K : Type} [Field K] :
    ((cell s col).val : K) = liftU (K := K) s.val[col.val]!+
      liftU s.val[col.val+4]!+liftU s.val[col.val+8]!+liftU s.val[col.val+12]! := by
  rw [value]
  simp only [Nat.cast_add,liftU]

#print axioms value
#print axioms bound
#print axioms lift
end R1Z.PV_Src_ExternalSumValue
