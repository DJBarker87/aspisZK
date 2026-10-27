import JGk_TX2_Group2_08
set_option autoImplicit false
namespace AspisR1.JGk_TX2_Group2_07
open JGk_TX2_OrderTools
def group : List (Nat × Nat) := [(7,3328),(7,5120),(7,10624),(7,13952),(7,16000),(7,33152),(7,37504),(7,41600),(7,44288),(7,44928),(7,46464),(7,54272)]
theorem ordered : group.Pairwise le := by decide
#print axioms ordered
theorem height : ∀ x ∈ group, x.1=7 := by
  simp only [group,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false]
  intro x hx
  rcases hx with hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx
  all_goals subst x; rfl
#print axioms height
def stream := group++JGk_TX2_Group2_08.stream
theorem stream_ordered : stream.Pairwise le := by
  apply append_groups 7 group JGk_TX2_Group2_08.stream ordered JGk_TX2_Group2_08.stream_ordered height
  intro x hx
  have := JGk_TX2_Group2_08.lower x hx
  omega
theorem lower : ∀ x ∈ stream, 7≤x.1 := by
  intro x hx
  rcases List.mem_append.mp hx with hx|hx
  · have := height x hx; omega
  · have := JGk_TX2_Group2_08.lower x hx; omega
#print axioms stream_ordered
#print axioms lower
end AspisR1.JGk_TX2_Group2_07
