import FJf_ArraySlots
import FJc_ReadSlot
set_option autoImplicit false
namespace AspisR1.FJf_U64Array
open Aeneas Aeneas.Std Result

def cell {N : Usize} (a : Array U64 N) (j : Nat) : U64 := a.val[j]?.getD 0#u64

theorem read {N : Usize} (a : Array U64 N) (i : Usize) (x : U64)
    (run : Array.index_usize a i=ok x) : cell a i.val=x := by
  simp only [cell,FJc_ReadSlot.slot _ _ _ run,Option.getD_some]

theorem update {N : Usize} (a b : Array U64 N) (i : Usize) (x : U64)
    (run : Array.update a i x=ok b) (j : Nat) :
    cell b j=if i.val=j then x else cell a j := by
  unfold cell
  rw [FJf_ArraySlots.update_slot a b i x run j]
  by_cases h : i.val=j
  · simp only [if_pos h,Option.getD_some]
  · simp only [if_neg h]
#print axioms read
#print axioms update
end AspisR1.FJf_U64Array
