import JGk_TX2_Group2_12
set_option autoImplicit false
namespace AspisR1.JGk_TX2_Group2_11
open JGk_TX2_OrderTools
def group : List (Nat × Nat) := [(11,0),(11,6144),(11,8192),(11,34816),(11,38912),(11,47104),(11,55296)]
theorem ordered : group.Pairwise le := by decide
#print axioms ordered
theorem height : ∀ x ∈ group, x.1=11 := by
  simp only [group,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false]
  intro x hx
  rcases hx with hx | hx | hx | hx | hx | hx | hx
  all_goals subst x; rfl
#print axioms height
def stream := group++JGk_TX2_Group2_12.stream
theorem stream_ordered : stream.Pairwise le := by
  apply append_groups 11 group JGk_TX2_Group2_12.stream ordered JGk_TX2_Group2_12.stream_ordered height
  intro x hx
  have := JGk_TX2_Group2_12.lower x hx
  omega
theorem lower : ∀ x ∈ stream, 11≤x.1 := by
  intro x hx
  rcases List.mem_append.mp hx with hx|hx
  · have := height x hx; omega
  · have := JGk_TX2_Group2_12.lower x hx; omega
#print axioms stream_ordered
#print axioms lower
end AspisR1.JGk_TX2_Group2_11
