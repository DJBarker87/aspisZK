import JGk_TX2_Group2_16
set_option autoImplicit false
namespace AspisR1.JGk_TX2_Group2_15
open JGk_TX2_OrderTools
def group : List (Nat × Nat) := []
theorem ordered : group.Pairwise le := by decide
#print axioms ordered
theorem height : ∀ x ∈ group, x.1=15 := by
  intro x hx
  simp only [group,List.not_mem_nil] at hx
#print axioms height
def stream := group++JGk_TX2_Group2_16.stream
theorem stream_ordered : stream.Pairwise le := by
  apply append_groups 15 group JGk_TX2_Group2_16.stream ordered JGk_TX2_Group2_16.stream_ordered height
  intro x hx
  have := JGk_TX2_Group2_16.lower x hx
  omega
theorem lower : ∀ x ∈ stream, 15≤x.1 := by
  intro x hx
  rcases List.mem_append.mp hx with hx|hx
  · have := height x hx; omega
  · have := JGk_TX2_Group2_16.lower x hx; omega
#print axioms stream_ordered
#print axioms lower
end AspisR1.JGk_TX2_Group2_15
