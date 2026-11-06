import NJB_Traverse
set_option autoImplicit false
namespace AspisR1.NJL_Traverse
open Aeneas Aeneas.Std Result
/-- Full ordered invocation/returned-list association. The generic child
interface is instantiated internally by each positive root, never retained as
a root assumption. Uses the predecessor traversal, not a duplicate emitter. -/
theorem packet {α β : Type} (f : α → Result β) (p : β → Prop) (R : α → β → Prop)
 (xs : List α) (child : ∀ x∈xs,∃ y,f x=ok y ∧ p y ∧ R x y) :
 ∃ ys,NJB_Traverse.run f xs=ok ys ∧ (∀ y∈ys.val,p y) ∧ List.Forall₂ R xs ys.val := by
 induction xs with
 | nil => exact ⟨⟨[],rfl⟩,rfl,by simp,.nil⟩
 | cons x xs ih =>
  obtain ⟨y,call,hy,relation⟩ := child x (by simp)
  obtain ⟨ys,rest,hs,relations⟩ := ih (fun z hz=>child z (by simp [hz]))
  refine ⟨⟨y::ys.val,by simp only [List.length_cons,ys.property]⟩,?_,?_,.cons relation relations⟩
  · simp only [NJB_Traverse.run,call,rest,bind_tc_ok]
  · intro z hz
    rcases List.mem_cons.mp hz with h|h
    · simpa only [h] using hy
    · exact hs z h
#print axioms packet
end AspisR1.NJL_Traverse
