import R1Z.ProverRwDictionaryConstants
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwSuccessOptions
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
-- Borrowing Option preserves its discriminant and payload in the source model.
def asRef {T : Type} (x : Option T) : Result (Option T) := .ok x

def isSomeAnd {T F : Type} (inst : core.ops.function.FnOnce F T Bool)
    (x : Option T) (f : F) : Result Bool :=
  match x with
  | none => .ok false
  | some value => inst.call_once f value

def optionEq {T : Type} (inst : core.cmp.PartialEq T T)
    (x y : Option T) : Result Bool :=
  match x,y with
  | none,none => .ok true
  | some a,some b => inst.eq a b
  | _,_ => .ok false

def resultMap {T E U F : Type} (inst : core.ops.function.FnOnce F T U)
    (x : core.result.Result T E) (f : F) : Result (core.result.Result U E) :=
  match x with
  | .Ok a => do let b ← inst.call_once f a; .ok (.Ok b)
  | .Err e => .ok (.Err e)

@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {ProverRwDictionaryConstants.selected ops with
    op5 := isSomeAnd, op6 := asRef, op8 := optionEq, op11 := resultMap}

theorem none_predicate (ops : ExternalFuns) {T F : Type}
    (inst : core.ops.function.FnOnce F T Bool) (f : F) :
    (selected ops).op5 inst none f = .ok false := rfl

theorem some_predicate (ops : ExternalFuns) {T F : Type}
    (inst : core.ops.function.FnOnce F T Bool) (a : T) (f : F) :
    (selected ops).op5 inst (some a) f = inst.call_once f a := rfl

theorem borrowed (ops : ExternalFuns) {T : Type} (x : Option T) :
    (selected ops).op6 x = .ok x := rfl

theorem eq_some (ops : ExternalFuns) {T : Type}
    (inst : core.cmp.PartialEq T T) (a b : T) :
    (selected ops).op8 inst (some a) (some b) = inst.eq a b := rfl

theorem map_error (ops : ExternalFuns) {T E U F : Type}
    (inst : core.ops.function.FnOnce F T U) (e : E) (f : F) :
    (selected ops).op11 inst (.Err e) f = .ok (.Err e) := rfl

theorem map_ok (ops : ExternalFuns) {T E U F : Type}
    (inst : core.ops.function.FnOnce F T U) (a : T) (f : F) :
    (selected ops).op11 (E := E) inst (.Ok a) f =
      (do let b ← inst.call_once f a; .ok (.Ok b)) := rfl
#print axioms none_predicate
#print axioms some_predicate
#print axioms borrowed
#print axioms eq_some
#print axioms map_error
#print axioms map_ok
end R1Z.ProverRwSuccessOptions
