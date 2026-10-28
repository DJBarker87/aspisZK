import Aeneas.Std
import Aeneas.Tactic.RustAttributes
namespace PV_B3P_RustResult
open Aeneas Aeneas.Std
set_option autoImplicit false

def bindR {α β E : Type} (x : Result (core.result.Result α E))
    (k : α → Result (core.result.Result β E)) : Result (core.result.Result β E) :=
  match x with
  | .ok (.Ok a) => k a
  | .ok (.Err e) => .ok (.Err e)
  | .fail e => .fail e
  | .div => .div

def mapR {α β E : Type} (f : α → β) (x : Result (core.result.Result α E)) :
    Result (core.result.Result β E) := bindR x (fun a => .ok (.Ok (f a)))

def collect {α E : Type} : List (Result (core.result.Result α E)) →
    Result (core.result.Result (List α) E)
  | [] => .ok (.Ok [])
  | x :: xs => bindR x (fun a => bindR (collect xs) (fun rest => .ok (.Ok (a :: rest))))

theorem bindR_assoc {α β γ E : Type} (x : Result (core.result.Result α E))
    (f : α → Result (core.result.Result β E))
    (g : β → Result (core.result.Result γ E)) :
    bindR (bindR x f) g = bindR x (fun a => bindR (f a) g) := by
  cases x with
  | ok r => cases r <;> rfl
  | fail e => rfl
  | div => rfl

theorem bindR_outer {ι α β E : Type} (x : Result ι)
    (f : ι → Result (core.result.Result α E))
    (g : α → Result (core.result.Result β E)) :
    bindR (do let a ← x; f a) g = (do let a ← x; bindR (f a) g) := by
  cases x <;> rfl

theorem mapR_outer {ι α β E : Type} (x : Result ι)
    (f : ι → Result (core.result.Result α E)) (g : α → β) :
    mapR g (do let a ← x; f a) = (do let a ← x; mapR g (f a)) :=
  bindR_outer x f _

theorem try_eq {α β E : Type} (r : core.result.Result α E)
    (k : α → Result (core.result.Result β E)) :
    (do
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue a => k a
      | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            β (core.convert.FromSame E) residual) =
      bindR (.ok r) k := by
  cases r <;> rfl

theorem try_bind_eq {α β E : Type} (x : Result (core.result.Result α E))
    (k : α → Result (core.result.Result β E)) :
    (do
      let r ← x
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue a => k a
      | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            β (core.convert.FromSame E) residual) = bindR x k := by
  cases x with
  | ok r => exact try_eq r k
  | fail e => rfl
  | div => rfl

theorem mapR_bindR {α β γ E : Type} (x : Result (core.result.Result α E))
    (f : α → Result (core.result.Result β E)) (g : β → γ) :
    mapR g (bindR x f) = bindR x (fun a => mapR g (f a)) := bindR_assoc x f _

theorem fail_tag {α β E : Type} (e : Aeneas.Std.Error)
    (f : α → Result (core.result.Result β E)) : bindR (.fail e) f = .fail e := rfl

theorem div_tag {α β E : Type} (f : α → Result (core.result.Result β E)) :
    bindR .div f = .div := rfl

theorem error_tag {α β E : Type} (e : E) (f : α → Result (core.result.Result β E)) :
    bindR (.ok (.Err e)) f = .ok (.Err e) := rfl

#print axioms bindR_assoc
#print axioms bindR_outer
#print axioms mapR_outer
#print axioms try_eq
#print axioms try_bind_eq
#print axioms mapR_bindR
#print axioms fail_tag
#print axioms div_tag
#print axioms error_tag
end PV_B3P_RustResult
