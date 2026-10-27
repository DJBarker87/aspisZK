import JGk_TX2_Group0_05
set_option autoImplicit false
namespace AspisR1.JGk_TX2_Group0_04
open JGk_TX2_OrderTools
def group : List (Nat × Nat) := [(4,14272),(4,21264),(4,42160),(4,55360),(4,63840),(4,132368),(4,149600),(4,166144),(4,178096),(4,179632),(4,185648),(4,218096)]
theorem ordered : group.Pairwise le := by decide
#print axioms ordered
theorem height : ∀ x ∈ group, x.1=4 := by
  simp only [group,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false]
  intro x hx
  rcases hx with hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx
  all_goals subst x; rfl
#print axioms height
def stream := group++JGk_TX2_Group0_05.stream
theorem stream_ordered : stream.Pairwise le := by
  apply append_groups 4 group JGk_TX2_Group0_05.stream ordered JGk_TX2_Group0_05.stream_ordered height
  intro x hx
  have := JGk_TX2_Group0_05.lower x hx
  omega
theorem lower : ∀ x ∈ stream, 4≤x.1 := by
  intro x hx
  rcases List.mem_append.mp hx with hx|hx
  · have := height x hx; omega
  · have := JGk_TX2_Group0_05.lower x hx; omega
#print axioms stream_ordered
#print axioms lower
end AspisR1.JGk_TX2_Group0_04
