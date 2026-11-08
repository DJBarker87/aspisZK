import NMX_R7_MagicNe241
set_option autoImplicit false
namespace NMX_R8_MagicGet
open Aeneas Aeneas.Std Result

def first (data : Slice U8) : Slice U8 :=
 ⟨data.val.take 4,by have h := data.property; simp only [List.length_take]; omega⟩

theorem four : (4#usize).val = 4 := by scalar_tac

theorem get (data : Slice U8) :
 core.slice.Slice.get (core.slice.index.SliceIndexRangeToUsizeSlice U8) data {«end» := 4#usize} =
 if 4 ≤ data.val.length then ok (some (first data)) else ok none := by
 unfold core.slice.Slice.get core.slice.index.SliceIndexRangeToUsizeSlice
 dsimp only
 unfold core.slice.index.SliceIndexRangeToUsizeSlice.get
 simp only [four]
 by_cases bound : 4 ≤ data.val.length
 · rw [if_pos bound,if_pos bound]
   apply congrArg ok
   apply congrArg some
   apply Subtype.ext
   simp only [first,List.slice,List.drop_zero,Nat.sub_zero]
 · rw [if_neg bound,if_neg bound]

#print axioms four
#print axioms get
end NMX_R8_MagicGet
