import NMT_345StepBase
set_option autoImplicit false
namespace NMT_R2_ResultTry
open Aeneas Aeneas.Std NMT_345
abbrev R (A : Type) := Result (core.result.Result A PE)

def pure {A : Type} (a : A) : R A := .ok (.Ok a)
def throw {A : Type} (e : PE) : R A := .ok (.Err e)
def bind {A B : Type} (r : R A) (next : A → R B) : R B := do
 let value ← r
 match value with | .Ok a => next a | .Err e => throw e

theorem assoc {A B C : Type} (r : R A) (f : A → R B) (g : B → R C) :
 bind (bind r f) g = bind r (fun a => bind (f a) g) := by
 cases r with
 | fail e => rfl
 | div => rfl
 | ok value => cases value <;> rfl

theorem pure_left {A B : Type} (a : A) (f : A → R B) : bind (pure a) f = f a := rfl

theorem outer {A B C : Type} (r : Result A) (f : A → R B) (g : B → R C) :
 bind (Aeneas.Std.bind r f) g = Aeneas.Std.bind r (fun a => bind (f a) g) := by cases r <;> rfl

theorem choose {A B : Type} (b : Bool) (x y : R A) (next : A → R B) :
 bind (if b then x else y) next = if b then bind x next else bind y next := by cases b <;> rfl

theorem throw_left {A B : Type} (e : PE) (f : A → R B) : bind (throw e) f = throw e := rfl

theorem tryStep_eq {A : Type} (r : R A) (next : A → Result Ret) :
 tryStep r next = bind r next := rfl
#print axioms assoc
#print axioms pure_left
#print axioms outer
#print axioms choose
#print axioms throw_left
#print axioms tryStep_eq
end NMT_R2_ResultTry
