import JGk_TX2_Group2_07
set_option autoImplicit false
namespace AspisR1.JGk_TX2_Group2_06
open JGk_TX2_OrderTools
def group : List (Nat × Nat) := [(6,3456),(6,5248),(6,10560),(6,13888),(6,15872),(6,33024),(6,37440),(6,41472),(6,44416),(6,44800),(6,46336),(6,54400)]
theorem ordered : group.Pairwise le := by decide
#print axioms ordered
theorem height : ∀ x ∈ group, x.1=6 := by
  simp only [group,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false]
  intro x hx
  rcases hx with hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx
  all_goals subst x; rfl
#print axioms height
def stream := group++JGk_TX2_Group2_07.stream
theorem stream_ordered : stream.Pairwise le := by
  apply append_groups 6 group JGk_TX2_Group2_07.stream ordered JGk_TX2_Group2_07.stream_ordered height
  intro x hx
  have := JGk_TX2_Group2_07.lower x hx
  omega
theorem lower : ∀ x ∈ stream, 6≤x.1 := by
  intro x hx
  rcases List.mem_append.mp hx with hx|hx
  · have := height x hx; omega
  · have := JGk_TX2_Group2_07.lower x hx; omega
#print axioms stream_ordered
#print axioms lower
end AspisR1.JGk_TX2_Group2_06
