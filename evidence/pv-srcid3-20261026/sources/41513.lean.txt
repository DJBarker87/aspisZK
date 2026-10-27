import R1Z.PV_Src_ExternalBlockWrite

set_option autoImplicit false
namespace R1Z.PV_Src_ExternalWritePrefix
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_ExternalBlockStep

theorem extend (a b : State) (g : Usize) (hg : g.val < 4)
    (m : Array U32 4#usize)
    (h : ∀ j, j < 4*g.val → a.val[j]! = b.val[j]!) :
    ∀ j, j < 4*(Usize.wrapping_add g 1#usize).val →
      (write a g m).val[j]! = (write b g m).val[j]! := by
  intro j hj
  have hn := BuilderRecordsArray.next_val g (by omega)
  rw [hn] at hj
  by_cases prior : j < 4*g.val
  · rw [PV_Src_ExternalBlockWrite.other a g hg m j (Or.inl prior),
      PV_Src_ExternalBlockWrite.other b g hg m j (Or.inl prior)]
    exact h j prior
  · unfold write
    simp only [BuilderRecordsArray.set_get _ _ _ j
      (show (Usize.wrapping_add (base g) 3#usize).val < (16#usize : Usize).val by
        rw [offset_val g hg _ (by decide)];simp;omega),
      BuilderRecordsArray.set_get _ _ _ j
      (show (Usize.wrapping_add (base g) 2#usize).val < (16#usize : Usize).val by
        rw [offset_val g hg _ (by decide)];simp;omega),
      BuilderRecordsArray.set_get _ _ _ j
      (show (Usize.wrapping_add (base g) 1#usize).val < (16#usize : Usize).val by
        rw [offset_val g hg _ (by decide)];simp;omega),
      BuilderRecordsArray.set_get _ _ _ j
      (show (base g).val < (16#usize : Usize).val by rw [base_val g hg];simp;omega)]
    rw [offset_val g hg _ (by decide),offset_val g hg _ (by decide),
      offset_val g hg _ (by decide),base_val g hg]
    split <;> (try rfl)
    split <;> (try rfl)
    split <;> (try rfl)
    rw [if_pos (by omega)]

#print axioms extend
end R1Z.PV_Src_ExternalWritePrefix
