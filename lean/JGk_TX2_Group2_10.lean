import JGk_TX2_Group2_11
set_option autoImplicit false
namespace AspisR1.JGk_TX2_Group2_10
open JGk_TX2_OrderTools
def group : List (Nat × Nat) := [(10,2048),(10,4096),(10,11264),(10,12288),(10,14336),(10,33792),(10,37888),(10,41984),(10,43008),(10,45056),(10,53248)]
theorem ordered : group.Pairwise le := by decide
#print axioms ordered
theorem height : ∀ x ∈ group, x.1=10 := by
  simp only [group,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false]
  intro x hx
  rcases hx with hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx
  all_goals subst x; rfl
#print axioms height
def stream := group++JGk_TX2_Group2_11.stream
theorem stream_ordered : stream.Pairwise le := by
  apply append_groups 10 group JGk_TX2_Group2_11.stream ordered JGk_TX2_Group2_11.stream_ordered height
  intro x hx
  have := JGk_TX2_Group2_11.lower x hx
  omega
theorem lower : ∀ x ∈ stream, 10≤x.1 := by
  intro x hx
  rcases List.mem_append.mp hx with hx|hx
  · have := height x hx; omega
  · have := JGk_TX2_Group2_11.lower x hx; omega
#print axioms stream_ordered
#print axioms lower
end AspisR1.JGk_TX2_Group2_10
