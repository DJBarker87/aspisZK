import PV_B3P_FromFnFour550227
namespace PV_B3P_Association550227
open Aeneas Aeneas.Std
set_option autoImplicit false

theorem four_index_zero550 {α : Type} (a b c d : α) :
    Array.index_usize (Array.make 4#usize [a,b,c,d] (by simp)) 0#usize = .ok a := rfl
theorem four_index_one550 {α : Type} (a b c d : α) :
    Array.index_usize (Array.make 4#usize [a,b,c,d] (by simp)) 1#usize = .ok b := rfl
theorem four_index_two550 {α : Type} (a b c d : α) :
    Array.index_usize (Array.make 4#usize [a,b,c,d] (by simp)) 2#usize = .ok c := rfl
theorem four_index_three550 {α : Type} (a b c d : α) :
    Array.index_usize (Array.make 4#usize [a,b,c,d] (by simp)) 3#usize = .ok d := rfl

theorem ignored_four_read_zero550 {α β : Type} (xs : Array α 4#usize) (next : Result β) :
    (do let _ ← Array.index_usize xs 0#usize; next) = next :=
  ignored_total_continuation550 _ (PV_B3P_Success227.index xs _ (by decide)) next
theorem ignored_four_read_one550 {α β : Type} (xs : Array α 4#usize) (next : Result β) :
    (do let _ ← Array.index_usize xs 1#usize; next) = next :=
  ignored_total_continuation550 _ (PV_B3P_Success227.index xs _ (by decide)) next
theorem ignored_four_read_two550 {α β : Type} (xs : Array α 4#usize) (next : Result β) :
    (do let _ ← Array.index_usize xs 2#usize; next) = next :=
  ignored_total_continuation550 _ (PV_B3P_Success227.index xs _ (by decide)) next
theorem ignored_four_read_three550 {α β : Type} (xs : Array α 4#usize) (next : Result β) :
    (do let _ ← Array.index_usize xs 3#usize; next) = next :=
  ignored_total_continuation550 _ (PV_B3P_Success227.index xs _ (by decide)) next

#print axioms four_index_zero550
#print axioms four_index_one550
#print axioms four_index_two550
#print axioms four_index_three550
#print axioms ignored_four_read_zero550
#print axioms ignored_four_read_one550
#print axioms ignored_four_read_two550
#print axioms ignored_four_read_three550
end PV_B3P_Association550227
