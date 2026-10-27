import JGk_TX2_Group2_01
set_option autoImplicit false
namespace AspisR1.JGk_TX2_Group2_00
open JGk_TX2_OrderTools
def group : List (Nat × Nat) := [(0,3575),(0,5313),(0,10538),(0,13845),(0,15964),(0,33089),(0,37407),(0,41540),(0,44521),(0,44904),(0,46408),(0,54522)]
theorem ordered : group.Pairwise le := by decide
#print axioms ordered
theorem height : ∀ x ∈ group, x.1=0 := by
  simp only [group,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false]
  intro x hx
  rcases hx with hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx
  all_goals subst x; rfl
#print axioms height
def stream := group++JGk_TX2_Group2_01.stream
theorem stream_ordered : stream.Pairwise le := by
  apply append_groups 0 group JGk_TX2_Group2_01.stream ordered JGk_TX2_Group2_01.stream_ordered height
  intro x hx
  have := JGk_TX2_Group2_01.lower x hx
  omega
theorem lower : ∀ x ∈ stream, 0≤x.1 := by
  intro x hx
  rcases List.mem_append.mp hx with hx|hx
  · have := height x hx; omega
  · have := JGk_TX2_Group2_01.lower x hx; omega
#print axioms stream_ordered
#print axioms lower
end AspisR1.JGk_TX2_Group2_00
