import JGk_TX2_Group0_06
set_option autoImplicit false
namespace AspisR1.JGk_TX2_Group0_05
open JGk_TX2_OrderTools
def group : List (Nat × Nat) := [(5,14304),(5,21280),(5,42112),(5,55392),(5,63808),(5,132384),(5,149568),(5,166176),(5,178048),(5,179584),(5,185600),(5,218048)]
theorem ordered : group.Pairwise le := by decide
#print axioms ordered
theorem height : ∀ x ∈ group, x.1=5 := by
  simp only [group,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false]
  intro x hx
  rcases hx with hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx
  all_goals subst x; rfl
#print axioms height
def stream := group++JGk_TX2_Group0_06.stream
theorem stream_ordered : stream.Pairwise le := by
  apply append_groups 5 group JGk_TX2_Group0_06.stream ordered JGk_TX2_Group0_06.stream_ordered height
  intro x hx
  have := JGk_TX2_Group0_06.lower x hx
  omega
theorem lower : ∀ x ∈ stream, 5≤x.1 := by
  intro x hx
  rcases List.mem_append.mp hx with hx|hx
  · have := height x hx; omega
  · have := JGk_TX2_Group0_06.lower x hx; omega
#print axioms stream_ordered
#print axioms lower
end AspisR1.JGk_TX2_Group0_05
