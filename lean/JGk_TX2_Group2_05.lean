import JGk_TX2_Group2_06
set_option autoImplicit false
namespace AspisR1.JGk_TX2_Group2_05
open JGk_TX2_OrderTools
def group : List (Nat × Nat) := [(5,3520),(5,5344),(5,10496),(5,13856),(5,15968),(5,33120),(5,37408),(5,41568),(5,44480),(5,44864),(5,46432),(5,54464)]
theorem ordered : group.Pairwise le := by decide
#print axioms ordered
theorem height : ∀ x ∈ group, x.1=5 := by
  simp only [group,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false]
  intro x hx
  rcases hx with hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx
  all_goals subst x; rfl
#print axioms height
def stream := group++JGk_TX2_Group2_06.stream
theorem stream_ordered : stream.Pairwise le := by
  apply append_groups 5 group JGk_TX2_Group2_06.stream ordered JGk_TX2_Group2_06.stream_ordered height
  intro x hx
  have := JGk_TX2_Group2_06.lower x hx
  omega
theorem lower : ∀ x ∈ stream, 5≤x.1 := by
  intro x hx
  rcases List.mem_append.mp hx with hx|hx
  · have := height x hx; omega
  · have := JGk_TX2_Group2_06.lower x hx; omega
#print axioms stream_ordered
#print axioms lower
end AspisR1.JGk_TX2_Group2_05
