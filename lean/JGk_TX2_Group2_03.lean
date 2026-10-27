import JGk_TX2_Group2_04
set_option autoImplicit false
namespace AspisR1.JGk_TX2_Group2_03
open JGk_TX2_OrderTools
def group : List (Nat × Nat) := [(3,3576),(3,5320),(3,10528),(3,13848),(3,15952),(3,33096),(3,37392),(3,41544),(3,44512),(3,44896),(3,46400),(3,54512)]
theorem ordered : group.Pairwise le := by decide
#print axioms ordered
theorem height : ∀ x ∈ group, x.1=3 := by
  simp only [group,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false]
  intro x hx
  rcases hx with hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx
  all_goals subst x; rfl
#print axioms height
def stream := group++JGk_TX2_Group2_04.stream
theorem stream_ordered : stream.Pairwise le := by
  apply append_groups 3 group JGk_TX2_Group2_04.stream ordered JGk_TX2_Group2_04.stream_ordered height
  intro x hx
  have := JGk_TX2_Group2_04.lower x hx
  omega
theorem lower : ∀ x ∈ stream, 3≤x.1 := by
  intro x hx
  rcases List.mem_append.mp hx with hx|hx
  · have := height x hx; omega
  · have := JGk_TX2_Group2_04.lower x hx; omega
#print axioms stream_ordered
#print axioms lower
end AspisR1.JGk_TX2_Group2_03
