import R1Z.PV_RE_NoCatchCore
set_option autoImplicit false
namespace R1Z.PV_RE_SourceContexts
open Aeneas.Std PV_RE_NoCatchCore
/-- A reached prefix equation; its left side is the actual source expression.
The generator supplies every prefix equation, rather than discarding it. -/
theorem bind_ok {α β : Type} (x : Result α) (v : α) (k : α → Result β)
    (h : x = .ok v) : (x >>= k) = k v := by rw [h]; rfl

theorem bind_fail {α β : Type} (x : Result α) (k : α → Result β)
    (e : Error) (h : x = .fail e) : (x >>= k) = .fail e := by rw [h]; rfl

theorem bind_div {α β : Type} (x : Result α) (k : α → Result β)
    (h : x = .div) : (x >>= k) = .div := by rw [h]; rfl

/-- Extend a proven source prefix to the next reached expression. -/
theorem prefix_step {α β γ : Type} (whole : Result γ) (x : Result α)
    (k : α → Result β) (outer : Result β → Result γ) (v : α)
    (context : whole = outer (x >>= k)) (hprefix : x = .ok v) :
    whole = outer (k v) := by rw [context, bind_ok x v k hprefix]

/-- A complete context transports the poisoned result, including all ancestors. -/
theorem context_failure {α β : Type} (whole : Result β) (call : Result α)
    (outer : Result α → Result β) (e : Error)
    (context : whole = outer call) (forward : NoCatch outer)
    (poison : call = .fail e) : whole = .fail e := by
  rw [context, poison, forward.1 e]

theorem context_divergence {α β : Type} (whole : Result β) (call : Result α)
    (outer : Result α → Result β)
    (context : whole = outer call) (forward : NoCatch outer)
    (poison : call = .div) : whole = .div := by
  rw [context, poison, forward.2]

#print axioms bind_ok
#print axioms bind_fail
#print axioms bind_div
#print axioms prefix_step
#print axioms context_failure
#print axioms context_divergence
end R1Z.PV_RE_SourceContexts
