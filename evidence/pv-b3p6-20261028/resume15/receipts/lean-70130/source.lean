import PV_B3P_RangeFold13227
namespace PV_B3P_Native15227
open Aeneas Aeneas.Std PV_B3P_Binding9227 PV_B3P_Binding11227 PV_B3P_Binding13227 Result
set_option autoImplicit false

theorem fold_pointwise15 {α β : Type} (left right : α → β → Result α)
    (indices : List β) (state : α)
    (same : ∀ index ∈ indices, ∀ state, left state index = right state index) :
    PV_B3P_Ordered227.fold left indices state = PV_B3P_Ordered227.fold right indices state := by
  induction indices generalizing state with
  | nil => rfl
  | cons index rest ih =>
    simp only [PV_B3P_Ordered227.fold]
    rw [same index (by simp)]
    apply congrArg (Aeneas.Std.bind _)
    funext next
    exact ih next (fun i member => same i (by simp only [List.mem_cons]; exact Or.inr member))

theorem indices_bound_sixteen15 (index : Usize) (member : index ∈ usize_indices11 16 0#usize) : index.val < 16 := by
  rw [indices_sixteen13] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
  all_goals subst index; decide
#print axioms fold_pointwise15
#print axioms indices_bound_sixteen15
end PV_B3P_Native15227
