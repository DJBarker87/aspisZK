import JGk_TX2_OrderTools
set_option autoImplicit false
namespace AspisR1.JGk_TX2_Group2_17
open JGk_TX2_OrderTools
def group : List (Nat × Nat) := [(17,131072)]
theorem ordered : group.Pairwise le := by decide
#print axioms ordered
theorem height : ∀ x ∈ group, x.1=17 := by
  simp only [group,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false]
  intro x hx
  rcases hx with hx
  all_goals subst x; rfl
#print axioms height
def stream := group++[]
theorem stream_ordered : stream.Pairwise le := by
  simpa only [stream,List.append_nil] using ordered
theorem lower : ∀ x ∈ stream, 17≤x.1 := by
  intro x hx
  have e:=height x (by simpa only [stream,List.append_nil] using hx)
  omega
#print axioms stream_ordered
#print axioms lower
end AspisR1.JGk_TX2_Group2_17
