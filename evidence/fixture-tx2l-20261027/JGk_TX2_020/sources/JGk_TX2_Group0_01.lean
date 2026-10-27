import JGk_TX2_Group0_02
set_option autoImplicit false
namespace AspisR1.JGk_TX2_Group0_01
open JGk_TX2_OrderTools
def group : List (Nat × Nat) := [(1,14298),(1,21250),(1,42156),(1,55378),(1,63862),(1,132352),(1,149626),(1,166166),(1,178082),(1,179620),(1,185638),(1,218092)]
theorem ordered : group.Pairwise le := by decide
#print axioms ordered
theorem height : ∀ x ∈ group, x.1=1 := by
  simp only [group,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false]
  intro x hx
  rcases hx with hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx
  all_goals subst x; rfl
#print axioms height
def stream := group++JGk_TX2_Group0_02.stream
theorem stream_ordered : stream.Pairwise le := by
  apply append_groups 1 group JGk_TX2_Group0_02.stream ordered JGk_TX2_Group0_02.stream_ordered height
  intro x hx
  have := JGk_TX2_Group0_02.lower x hx
  omega
theorem lower : ∀ x ∈ stream, 1≤x.1 := by
  intro x hx
  rcases List.mem_append.mp hx with hx|hx
  · have := height x hx; omega
  · have := JGk_TX2_Group0_02.lower x hx; omega
#print axioms stream_ordered
#print axioms lower
end AspisR1.JGk_TX2_Group0_01
