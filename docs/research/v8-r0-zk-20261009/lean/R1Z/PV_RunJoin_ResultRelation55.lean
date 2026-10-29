import R1Z.ProverRwFullFuns
set_option autoImplicit false
namespace R1Z.PV_RunJoin_ResultRelation55
open Aeneas Aeneas.Std Result

inductive Rel {A B : Type} (R : A → B → Prop) : Result A → Result B → Prop
  | ok {a b} : R a b → Rel R (.ok a) (.ok b)
  | fail (e : Error) : Rel R (.fail e) (.fail e)
  | div : Rel R .div .div

inductive CoreRel {A B E : Type} (R : A → B → Prop) : core.result.Result A E → core.result.Result B E → Prop
  | ok {a b} : R a b → CoreRel R (.Ok a) (.Ok b)
  | err (e : E) : CoreRel R (.Err e) (.Err e)

theorem same_bind {A B C : Type} (R : B → C → Prop) (m : Result A)
    (f : A → Result B) (g : A → Result C) (step : ∀ a,Rel R (f a) (g a)) :
    Rel R (m >>= f) (m >>= g) := by
  cases m with
  | ok a => exact step a
  | fail e => exact .fail e
  | div => exact .div

theorem bind {A B C D : Type} (R : A → B → Prop) (S : C → D → Prop)
    (m : Result A) (n : Result B) (f : A → Result C) (g : B → Result D)
    (prefix : Rel R m n) (step : ∀ a b,R a b → Rel S (f a) (g b)) :
    Rel S (m >>= f) (n >>= g) := by
  cases prefix with
  | ok r => exact step _ _ r
  | fail e => exact .fail e
  | div => exact .div

theorem equality {A : Type} {m n : Result A} (h : Rel Eq m n) : m=n := by
  cases h with
  | ok r => exact congrArg Result.ok r
  | fail e => rfl
  | div => rfl
#print axioms Rel
#print axioms CoreRel
#print axioms same_bind
#print axioms bind
#print axioms equality
end R1Z.PV_RunJoin_ResultRelation55
