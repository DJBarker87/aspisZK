import JGk_TX2_Group0_03
set_option autoImplicit false
namespace AspisR1.JGk_TX2_Group0_02
open JGk_TX2_OrderTools
def group : List (Nat × Nat) := [(2,14300),(2,21252),(2,42152),(2,55380),(2,63856),(2,132356),(2,149628),(2,166160),(2,178084),(2,179616),(2,185632),(2,218088)]
theorem ordered : group.Pairwise le := by decide
#print axioms ordered
theorem height : ∀ x ∈ group, x.1=2 := by
  simp only [group,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false]
  intro x hx
  rcases hx with hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx
  all_goals subst x; rfl
#print axioms height
def stream := group++JGk_TX2_Group0_03.stream
theorem stream_ordered : stream.Pairwise le := by
  apply append_groups 2 group JGk_TX2_Group0_03.stream ordered JGk_TX2_Group0_03.stream_ordered height
  intro x hx
  have := JGk_TX2_Group0_03.lower x hx
  omega
theorem lower : ∀ x ∈ stream, 2≤x.1 := by
  intro x hx
  rcases List.mem_append.mp hx with hx|hx
  · have := height x hx; omega
  · have := JGk_TX2_Group0_03.lower x hx; omega
#print axioms stream_ordered
#print axioms lower
end AspisR1.JGk_TX2_Group0_02
