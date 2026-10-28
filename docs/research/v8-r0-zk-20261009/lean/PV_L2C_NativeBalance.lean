import PV_L2C_NativeFold
import Mathlib.Tactic.Abel
set_option autoImplicit false
namespace PV_L2C_NativeBalance
open PV_L2C_M31 PV_L2C_NativeFold
/-- The inactive row sequence split at the dependent cell. This is the exact
final store of balance_m31_copy_inactive, retaining native row order. -/
def rebalance (before after : List word) : List word :=
  before ++ sub 0 (fold (before++after) 0) :: after

theorem rebalance_canonical (before after : List word)
    (hb : ∀ x ∈ before, canonical x) (ha : ∀ x ∈ after, canonical x) :
    ∀ x ∈ rebalance before after, canonical x := by
  have hc : ∀ x ∈ before++after, canonical x := by
    intro x hx
    rcases List.mem_append.mp hx with hx|hx
    · exact hb x hx
    · exact ha x hx
  intro x hx
  rcases List.mem_append.mp hx with hx|hx
  · exact hb x hx
  · rcases List.mem_cons.mp hx with rfl|hx
    · exact (negate_decode _ hc).1
    · exact ha x hx
#print axioms rebalance_canonical

theorem rebalance_decode_sum (before after : List word)
    (hb : ∀ x ∈ before, canonical x) (ha : ∀ x ∈ after, canonical x) :
    ((rebalance before after).map decode).sum=0 := by
  have hc : ∀ x ∈ before++after, canonical x := by
    intro x hx
    rcases List.mem_append.mp hx with hx|hx
    · exact hb x hx
    · exact ha x hx
  have hn := (negate_decode (before++after) hc).2
  simp only [rebalance,List.map_append,List.map_cons,List.sum_append,List.sum_cons] at *
  rw [hn]
  abel
#print axioms rebalance_decode_sum

theorem audit_zero (before after : List word)
    (hb : ∀ x ∈ before, canonical x) (ha : ∀ x ∈ after, canonical x) :
    fold (rebalance before after) 0=0 := by
  apply decode_injective _ 0
  · exact fold_canonical _ (rebalance_canonical before after hb ha) 0 (by unfold canonical p; decide)
  · unfold canonical p; decide
  · rw [fold_zero_decode _ (rebalance_canonical before after hb ha),rebalance_decode_sum before after hb ha]
    rfl
#print axioms audit_zero

theorem audit_branch (before after : List word)
    (hb : ∀ x ∈ before, canonical x) (ha : ∀ x ∈ after, canonical x) :
    decide (fold (rebalance before after) 0≠0)=false := by
  rw [audit_zero before after hb ha]
  rfl
#print axioms audit_branch
end PV_L2C_NativeBalance
