import JGk_TX2_Group0_07
set_option autoImplicit false
namespace AspisR1.JGk_TX2_Group0_06
open JGk_TX2_OrderTools
def group : List (Nat × Nat) := [(6,14208),(6,21312),(6,42176),(6,55296),(6,63744),(6,132416),(6,149504),(6,166208),(6,178112),(6,179648),(6,185664),(6,217984)]
theorem ordered : group.Pairwise le := by decide
#print axioms ordered
theorem height : ∀ x ∈ group, x.1=6 := by
  simp only [group,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false]
  intro x hx
  rcases hx with hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx
  all_goals subst x; rfl
#print axioms height
def stream := group++JGk_TX2_Group0_07.stream
theorem stream_ordered : stream.Pairwise le := by
  apply append_groups 6 group JGk_TX2_Group0_07.stream ordered JGk_TX2_Group0_07.stream_ordered height
  intro x hx
  have := JGk_TX2_Group0_07.lower x hx
  omega
theorem lower : ∀ x ∈ stream, 6≤x.1 := by
  intro x hx
  rcases List.mem_append.mp hx with hx|hx
  · have := height x hx; omega
  · have := JGk_TX2_Group0_07.lower x hx; omega
#print axioms stream_ordered
#print axioms lower
end AspisR1.JGk_TX2_Group0_06
