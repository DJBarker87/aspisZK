import JGk_TX2_Group0_12
set_option autoImplicit false
namespace AspisR1.JGk_TX2_Group0_11
open JGk_TX2_OrderTools
def group : List (Nat × Nat) := [(11,14336),(11,22528),(11,43008),(11,53248),(11,61440),(11,133120),(11,147456),(11,163840),(11,186368),(11,219136)]
theorem ordered : group.Pairwise le := by decide
#print axioms ordered
theorem height : ∀ x ∈ group, x.1=11 := by
  simp only [group,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false]
  intro x hx
  rcases hx with hx | hx | hx | hx | hx | hx | hx | hx | hx | hx
  all_goals subst x; rfl
#print axioms height
def stream := group++JGk_TX2_Group0_12.stream
theorem stream_ordered : stream.Pairwise le := by
  apply append_groups 11 group JGk_TX2_Group0_12.stream ordered JGk_TX2_Group0_12.stream_ordered height
  intro x hx
  have := JGk_TX2_Group0_12.lower x hx
  omega
theorem lower : ∀ x ∈ stream, 11≤x.1 := by
  intro x hx
  rcases List.mem_append.mp hx with hx|hx
  · have := height x hx; omega
  · have := JGk_TX2_Group0_12.lower x hx; omega
#print axioms stream_ordered
#print axioms lower
end AspisR1.JGk_TX2_Group0_11
