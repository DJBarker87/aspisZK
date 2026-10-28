import R1Z.PV_RunJoin_ResultDomain28
set_option autoImplicit false
namespace R1Z.PV_RunJoin_ControlDomain28
open Aeneas Aeneas.Std Result PV_RunJoin_ResultDomain28

theorem ite_wp {α : Type} (p : Prop) [Decidable p] (a b : Result α) (q : α → Prop) :
    wp (if p then a else b) q ↔ if p then wp a q else wp b q := by
  by_cases h : p <;> simp only [h,↓reduceIte]
#print axioms ite_wp

theorem option_wp {α β : Type} (o : Option α) (n : Result β)
    (s : α → Result β) (q : β → Prop) :
    wp (match o with | none => n | some a => s a) q ↔
      match o with | none => wp n q | some a => wp (s a) q := by
  cases o <;> rfl
#print axioms option_wp

theorem flow_wp {α β γ : Type} (o : core.ops.control_flow.ControlFlow α β)
    (b : α → Result γ) (c : β → Result γ) (q : γ → Prop) :
    wp (match o with | .Break a => b a | .Continue a => c a) q ↔
      match o with | .Break a => wp (b a) q | .Continue a => wp (c a) q := by
  cases o <;> rfl
#print axioms flow_wp
end R1Z.PV_RunJoin_ControlDomain28
