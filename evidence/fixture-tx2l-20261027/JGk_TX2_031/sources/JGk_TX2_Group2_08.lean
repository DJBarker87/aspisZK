import JGk_TX2_Group2_09
set_option autoImplicit false
namespace AspisR1.JGk_TX2_Group2_08
open JGk_TX2_OrderTools
def group : List (Nat × Nat) := [(8,3072),(8,5376),(8,10240),(8,14080),(8,16128),(8,32768),(8,37632),(8,41728),(8,44032),(8,44544),(8,46080),(8,54528)]
theorem ordered : group.Pairwise le := by decide
#print axioms ordered
theorem height : ∀ x ∈ group, x.1=8 := by
  simp only [group,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false]
  intro x hx
  rcases hx with hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx
  all_goals subst x; rfl
#print axioms height
def stream := group++JGk_TX2_Group2_09.stream
theorem stream_ordered : stream.Pairwise le := by
  apply append_groups 8 group JGk_TX2_Group2_09.stream ordered JGk_TX2_Group2_09.stream_ordered height
  intro x hx
  have := JGk_TX2_Group2_09.lower x hx
  omega
theorem lower : ∀ x ∈ stream, 8≤x.1 := by
  intro x hx
  rcases List.mem_append.mp hx with hx|hx
  · have := height x hx; omega
  · have := JGk_TX2_Group2_09.lower x hx; omega
#print axioms stream_ordered
#print axioms lower
end AspisR1.JGk_TX2_Group2_08
