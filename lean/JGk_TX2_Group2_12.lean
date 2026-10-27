import JGk_TX2_Group2_13
set_option autoImplicit false
namespace AspisR1.JGk_TX2_Group2_12
open JGk_TX2_OrderTools
def group : List (Nat × Nat) := [(12,49152)]
theorem ordered : group.Pairwise le := by decide
#print axioms ordered
theorem height : ∀ x ∈ group, x.1=12 := by
  simp only [group,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false]
  intro x hx
  rcases hx with hx
  all_goals subst x; rfl
#print axioms height
def stream := group++JGk_TX2_Group2_13.stream
theorem stream_ordered : stream.Pairwise le := by
  apply append_groups 12 group JGk_TX2_Group2_13.stream ordered JGk_TX2_Group2_13.stream_ordered height
  intro x hx
  have := JGk_TX2_Group2_13.lower x hx
  omega
theorem lower : ∀ x ∈ stream, 12≤x.1 := by
  intro x hx
  rcases List.mem_append.mp hx with hx|hx
  · have := height x hx; omega
  · have := JGk_TX2_Group2_13.lower x hx; omega
#print axioms stream_ordered
#print axioms lower
end AspisR1.JGk_TX2_Group2_12
