import PV_B3P_NativePreweighted15227
namespace PV_B3P_Caller15227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false

def PreweightedCall15 (start count : Nat) : Prop :=
  (start=0 ∧ count=16) ∨ (start=16 ∧ count=16) ∨ (start=32 ∧ count=17) ∨
  (start=49 ∧ count=33) ∨ (start=82 ∧ count=2) ∨ (start=0 ∧ count=12) ∨
  (start=84 ∧ count=8) ∨ (start=92 ∧ count=2)

theorem preweighted_source_call_bounds15 (start count : Nat) (called : PreweightedCall15 start count) :
    0 < count ∧ start+count ≤ 96 ∧ (start+count-1)/4 < 24 := by
  unfold PreweightedCall15 at called
  rcases called with h|h|h|h|h|h|h|h
  all_goals rcases h with ⟨hs,hn⟩; subst start; subst count; decide

theorem preweighted_window_source_index15 (start count group slot : Nat)
    (slot_bound : slot < 4) (selected : start ≤ 4*group+slot ∧ 4*group+slot < start+count) :
    4*group+slot-start < count := by omega

/-- Only the selected arm reads values[source-start]; the ZERO arm performs
no values read. The call bound makes the final inclusive increment safe. -/
theorem preweighted_source_group_successor15 (start count group : Nat)
    (called : PreweightedCall15 start count) (group_bound : group ≤ (start+count-1)/4) :
    group+1 ≤ 24 := by
  have bound := preweighted_source_call_bounds15 start count called
  omega
#print axioms preweighted_source_call_bounds15
#print axioms preweighted_window_source_index15
#print axioms preweighted_source_group_successor15
end PV_B3P_Caller15227
