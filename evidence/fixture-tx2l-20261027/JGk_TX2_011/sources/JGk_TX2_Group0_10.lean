import JGk_TX2_Group0_11
set_option autoImplicit false
namespace AspisR1.JGk_TX2_Group0_10
open JGk_TX2_OrderTools
def group : List (Nat × Nat) := [(10,12288),(10,21504),(10,40960),(10,56320),(10,64512),(10,131072),(10,150528),(10,166912),(10,176128),(10,178176),(10,184320),(10,218112)]
theorem ordered : group.Pairwise le := by decide
#print axioms ordered
theorem height : ∀ x ∈ group, x.1=10 := by
  simp only [group,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false]
  intro x hx
  rcases hx with hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx
  all_goals subst x; rfl
#print axioms height
def stream := group++JGk_TX2_Group0_11.stream
theorem stream_ordered : stream.Pairwise le := by
  apply append_groups 10 group JGk_TX2_Group0_11.stream ordered JGk_TX2_Group0_11.stream_ordered height
  intro x hx
  have := JGk_TX2_Group0_11.lower x hx
  omega
theorem lower : ∀ x ∈ stream, 10≤x.1 := by
  intro x hx
  rcases List.mem_append.mp hx with hx|hx
  · have := height x hx; omega
  · have := JGk_TX2_Group0_11.lower x hx; omega
#print axioms stream_ordered
#print axioms lower
end AspisR1.JGk_TX2_Group0_10
