import KMX_CopyMeaning
import PCD_RequestBridge
set_option autoImplicit false
namespace PCD_CopyJoin
/-- The exact retained KMX VALUE specification, at one arbitrary copied
window and its disjoint frame. Native replacements/controls are separate
required certificates; this theorem is not a Rust-to-Lean refinement. -/
theorem window_and_frame {α : Type} (src dst : Nat → α) (start count : Nat) :
    (∀ k, start ≤ k ∧ k < start+count → KMX_CopyMeaning.loop src dst start count k = src k) ∧
    (∀ k, k < start ∨ start+count ≤ k → KMX_CopyMeaning.loop src dst start count k = dst k) := by
  constructor
  · intro k inside
    rw [KMX_CopyMeaning.loop_spec,if_pos inside]
  · intro k outside
    exact KMX_CopyMeaning.copy_frame src dst start count k outside

/-- Copying one typed record retains the complete value, not just one of its
fields. The loop bound is one; no large concrete recurrence is reduced. -/
theorem single_value {α : Type} (src dst : Nat → α) :
    KMX_CopyMeaning.loop src dst 0 1 0 = src 0 := by
  rw [KMX_CopyMeaning.copy_prefix,if_pos (by decide)]

theorem request_observation_join (x y : PCD_FrozenRequest.LocalRequest)
    (same : ∀ slot word byte,
      PCD_RequestBridge.observation x slot word byte = PCD_RequestBridge.observation y slot word byte) :
    x = y := PCD_RequestBridge.observations_complete x y same
#print axioms window_and_frame
#print axioms single_value
#print axioms request_observation_join
end PCD_CopyJoin
