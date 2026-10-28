import R1Z.PV_Join_Canonical5
set_option autoImplicit false
namespace R1Z.PV_Join_ResultInvariant5
open Aeneas Aeneas.Std Result

def Safe {α : Type} (p : α → Prop) (r : Result α) : Prop :=
  ∀ x, r = .ok x → p x

theorem ok {α : Type} (p : α → Prop) (x : α) (h : p x) : Safe p (.ok x) := by
  intro y he; cases he; exact h

theorem bind {α β : Type} (p : α → Prop) (q : β → Prop)
    (r : Result α) (f : α → Result β) (hr : Safe p r)
    (hf : ∀ x, p x → Safe q (f x)) : Safe q (r >>= f) := by
  cases r with
  | ok x => exact hf x (hr x rfl)
  | fail e => intro y he; cases he
  | div => intro y he; cases he

theorem bind_any {α β : Type} (q : β → Prop) (r : Result α) (f : α → Result β)
    (hf : ∀ x, Safe q (f x)) : Safe q (r >>= f) :=
  bind (fun _ => True) q r f (by intro x h; trivial) (by intro x _; exact hf x)

#print axioms ok
#print axioms bind
#print axioms bind_any
end R1Z.PV_Join_ResultInvariant5
