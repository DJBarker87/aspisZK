import JGk_TX2_Group0_14
set_option autoImplicit false
namespace AspisR1.JGk_TX2_Group0_13
open JGk_TX2_OrderTools
def group : List (Nat × Nat) := [(13,0),(13,24576),(13,32768),(13,139264),(13,155648),(13,188416),(13,221184)]
theorem ordered : group.Pairwise le := by decide
#print axioms ordered
theorem height : ∀ x ∈ group, x.1=13 := by
  simp only [group,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false]
  intro x hx
  rcases hx with hx | hx | hx | hx | hx | hx | hx
  all_goals subst x; rfl
#print axioms height
def stream := group++JGk_TX2_Group0_14.stream
theorem stream_ordered : stream.Pairwise le := by
  apply append_groups 13 group JGk_TX2_Group0_14.stream ordered JGk_TX2_Group0_14.stream_ordered height
  intro x hx
  have := JGk_TX2_Group0_14.lower x hx
  omega
theorem lower : ∀ x ∈ stream, 13≤x.1 := by
  intro x hx
  rcases List.mem_append.mp hx with hx|hx
  · have := height x hx; omega
  · have := JGk_TX2_Group0_14.lower x hx; omega
#print axioms stream_ordered
#print axioms lower
end AspisR1.JGk_TX2_Group0_13
