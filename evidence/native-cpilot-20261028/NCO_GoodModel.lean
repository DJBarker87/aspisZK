import NCO_WordDomain
import NCO_Inner
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NCO_GoodModel

theorem word (payload : Slice U8) (i j : Nat) (hj : j < 8) :
    NCO_GlobalWord.Good payload i j ↔
      let n := LPl_Kit_Bytes.le32 ((((payload.val.drop (32*i)).take 32).drop (4*j)).take 4)
      n < 2147483647 ∧ (j < 4 ∨ n = 0) := by
  have value := NCO_WordDomain.value payload i j hj
  unfold NCO_GlobalWord.Good
  constructor
  · rintro ⟨canonical,high⟩
    have cv : (NCO_GlobalWord.word payload i j).val < 2147483647 := canonical
    refine ⟨by simpa only [value] using cv,?_⟩
    rcases high with low | zero
    · exact Or.inl low
    · right
      have z := congrArg UScalar.val zero
      change (NCO_GlobalWord.word payload i j).val = 0 at z
      exact value.symm.trans z
  · rintro ⟨canonical,high⟩
    refine ⟨?_,?_⟩
    · change (NCO_GlobalWord.word payload i j).val < 2147483647
      simpa only [value] using canonical
    · rcases high with low | zero
      · exact Or.inl low
      · right
        apply UScalar.eq_of_val_eq
        change (NCO_GlobalWord.word payload i j).val = 0
        exact value.trans zero

theorem row (payload : Slice U8) (i : Nat) :
    NCO_Inner.GoodFrom payload i 0 ↔
      LPl_Kit_Bytes.validChunk 8 true ((payload.val.drop (32*i)).take 32) = true := by
  unfold NCO_Inner.GoodFrom LPl_Kit_Bytes.validChunk
  simp only [List.all_eq_true,List.mem_range,Bool.and_eq_true,Bool.not_true,Bool.false_or,decide_eq_true_eq]
  constructor
  · intro h j hj
    exact (word payload i j hj).mp (h j (by omega) hj)
  · intro h j _ hj
    exact (word payload i j hj).mpr (h j hj)

#print axioms word
#print axioms row
end NCO_GoodModel
