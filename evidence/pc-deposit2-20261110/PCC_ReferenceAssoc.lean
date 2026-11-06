import PCC_ReferenceLaws
set_option autoImplicit false
namespace PCC.Reference
open PCA
/-- Full state/event/Result associativity; abort and error prefixes retain
exactly their entered calls and never execute a suffix. -/
theorem bind_assoc {α β γ : Type} (r : Reference α)
    (f : α → Reference β) (g : β → Reference γ) :
    bind (bind r f) g = bind r (fun a => bind (f a) g) := by
  funext s
  cases h : (r s).reply with
  | error e => simp only [bind,h]
  | abort e => simp only [bind,h]
  | ok a =>
    cases h2 : (f a (r s).state).reply <;>
      simp only [bind,h,h2,List.append_assoc]
#print axioms bind_assoc
end PCC.Reference
