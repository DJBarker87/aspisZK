import JGk_TX2_Group0_04
set_option autoImplicit false
namespace AspisR1.JGk_TX2_Group0_03
open JGk_TX2_OrderTools
def group : List (Nat × Nat) := [(3,14288),(3,21256),(3,42144),(3,55384),(3,63864),(3,132360),(3,149616),(3,166168),(3,178088),(3,179624),(3,185640),(3,218080)]
theorem ordered : group.Pairwise le := by decide
#print axioms ordered
theorem height : ∀ x ∈ group, x.1=3 := by
  simp only [group,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false]
  intro x hx
  rcases hx with hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx
  all_goals subst x; rfl
#print axioms height
def stream := group++JGk_TX2_Group0_04.stream
theorem stream_ordered : stream.Pairwise le := by
  apply append_groups 3 group JGk_TX2_Group0_04.stream ordered JGk_TX2_Group0_04.stream_ordered height
  intro x hx
  have := JGk_TX2_Group0_04.lower x hx
  omega
theorem lower : ∀ x ∈ stream, 3≤x.1 := by
  intro x hx
  rcases List.mem_append.mp hx with hx|hx
  · have := height x hx; omega
  · have := JGk_TX2_Group0_04.lower x hx; omega
#print axioms stream_ordered
#print axioms lower
end AspisR1.JGk_TX2_Group0_03
