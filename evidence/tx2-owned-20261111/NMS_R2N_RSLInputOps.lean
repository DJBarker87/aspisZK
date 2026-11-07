import NMS_R2N_RSLGetterLink
import NLM_CheckedAddFacts
set_option autoImplicit false
namespace NMS_R2N_RSLInputOps
open Aeneas Aeneas.Std AdapterRw NMS_R2N_RSLPoolCarriers

theorem index (accounts_ : Accounts) (i : Usize) (selected : r1_pool_adapter.owned.OwnedAccount)
 (read : Slice.index_usize accounts_ i = .ok selected) :
 (accounts accounts_)[i.val]? = some (account selected) := by
 unfold Slice.index_usize at read
 rw [Slice.getElem?_Usize_eq] at read
 cases found : accounts_.val[i.val]? with
 | none => simp only [found] at read; cases read
 | some x =>
   simp only [found] at read
   cases read
   simp only [accounts,List.getElem?_map,found,Option.map_some]

theorem zero_value : (0#usize).val = 0 := by scalar_tac
theorem six_value : (6#usize).val = 6 := by scalar_tac

theorem seven_value : (7#usize).val = 7 := by scalar_tac

theorem count (accounts_ : Accounts) (guard : (Slice.len accounts_ != 7#usize) = false) :
 (accounts accounts_).length = 7 := by
 have same : Slice.len accounts_ = 7#usize := by
   apply eq_of_beq
   cases h : (Slice.len accounts_ == 7#usize) <;> simp_all [bne]
 have length := congrArg (fun x : Usize => x.val) same
 rw [accounts_length]
 simpa only [Slice.len_val,seven_value] using length

theorem afterstate_value : (688#usize).val = RSL.AFTERSTATE_BYTES := by
 change (688#usize).val = 688
 scalar_tac

#print axioms index
#print axioms zero_value
#print axioms six_value
#print axioms seven_value
#print axioms count
#print axioms afterstate_value
end NMS_R2N_RSLInputOps
