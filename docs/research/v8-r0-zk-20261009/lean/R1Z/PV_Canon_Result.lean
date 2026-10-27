import R1Z.PV_Canon_Carrier
set_option autoImplicit false
namespace R1Z.PV_Canon
open Aeneas Aeneas.Std Result
def Safe {α : Type} (p : α → Prop) (r : Result α) : Prop := ∀ x, r = .ok x → p x
 theorem safe_of_total {α : Type} {p : α → Prop} {r : Result α}
    (h : ∃ z, r = .ok z ∧ p z) : Safe p r := by
  obtain ⟨z,hz,hp⟩ := h
  intro x hx
  rw [hz] at hx
  cases hx
  exact hp
 theorem safe_bind {α β : Type} (p : α → Prop) (q : β → Prop)
    (r : Result α) (f : α → Result β) (hr : Safe p r)
    (hf : ∀ x, p x → Safe q (f x)) : Safe q (r >>= f) := by
  cases r with
  | ok x => exact hf x (hr x rfl)
  | fail e => intro y hy; cases hy
  | div => intro y hy; cases hy
 theorem safe_bind_any {α β : Type} (q : β → Prop) (r : Result α) (f : α → Result β)
    (hf : ∀ x, Safe q (f x)) : Safe q (r >>= f) :=
  safe_bind (fun _ => True) q r f (by intro x h; trivial) (by intro x _; exact hf x)
 theorem safe_ok {α : Type} (p : α → Prop) (x : α) (hx : p x) : Safe p (.ok x) := by
  intro z hz; cases hz; exact hx
#print axioms safe_of_total
#print axioms safe_bind
#print axioms safe_bind_any
#print axioms safe_ok
end R1Z.PV_Canon
