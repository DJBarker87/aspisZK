import PoolS2_Lanes
set_option autoImplicit false
namespace AspisR1.PoolS2_LaneFacts
open Aeneas Aeneas.Std Result PoolS2_PdaSource PoolS2_MasterValidation PoolS2_Lanes

def Valid (master : Key) (expected : Nat) : List Lane → Prop
  | [] => True
  | lane::rest => lane.master = master ∧ lane.lane_id.val = expected ∧
      lane.tree.next_leaf_index ≤ capacity ∧ Valid master (expected+1) rest

theorem accepted_iff (master : Key) (expected : Nat) (lanes : List Lane) :
    check master expected lanes = .Ok () ↔ Valid master expected lanes := by
  classical
  induction lanes generalizing expected with
  | nil => simp [check,Valid]
  | cons lane rest ih =>
    by_cases hm : lane.master = master <;>
      by_cases hi : lane.lane_id.val = expected <;>
      by_cases hb : lane.tree.next_leaf_index > capacity <;>
      simp_all [check,Valid,ih]
    have outside : ¬capacity.val < lane.tree.next_leaf_index.val := by omega
    simp [outside,ih]

theorem bounds (master : Key) (expected : Nat) (lanes : List Lane)
    (h : Valid master expected lanes) :
    ∀ lane ∈ lanes, lane.tree.next_leaf_index ≤ capacity := by
  induction lanes generalizing expected with
  | nil => simp
  | cons lane rest ih =>
    rcases h with ⟨_,_,bound,tail⟩
    simpa using And.intro bound (ih (expected+1) tail)

#print axioms accepted_iff
#print axioms bounds
end AspisR1.PoolS2_LaneFacts
