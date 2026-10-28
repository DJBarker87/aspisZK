import Aeneas
set_option autoImplicit false
namespace R1Z.PV_RW_DataProduct
open Aeneas Aeneas.Std

def first {A B V : Type} : core.result.Result (A × B) V → core.result.Result A V
  | .Ok pair => .Ok pair.1
  | .Err error => .Err error

def second {A B V : Type} : core.result.Result (A × B) V → core.result.Result B V
  | .Ok pair => .Ok pair.2
  | .Err error => .Err error

def observe {A B : Type} (projection : A → B) : Result A → Result B
  | .ok value => .ok (projection value)
  | .fail error => .fail error
  | .div => .div

theorem payload {A B V : Type} (left right : core.result.Result (A × B) V)
    (ha : first left=first right) (hb : second left=second right) : left=right := by
  cases left with
  | Err error => cases right <;> cases ha <;> rfl
  | Ok pair =>
    cases right with
    | Err error => cases ha
    | Ok other =>
      have a : pair.1=other.1 := core.result.Result.Ok.inj ha
      have b : pair.2=other.2 := core.result.Result.Ok.inj hb
      exact congrArg core.result.Result.Ok (Prod.ext a b)

theorem joint {A B V : Type} (left right : Result (core.result.Result (A × B) V))
    (ha : observe first left=observe first right)
    (hb : observe second left=observe second right) : left=right := by
  cases left with
  | fail error => cases right <;> cases ha <;> rfl
  | div => cases right <;> cases ha <;> rfl
  | ok pair =>
    cases right with
    | fail error => cases ha
    | div => cases ha
    | ok other => exact congrArg Result.ok (payload pair other (Result.ok.inj ha) (Result.ok.inj hb))

theorem equal_iff {A B V : Type} (left right : Result (core.result.Result (A × B) V)) :
    left=right ↔ (observe first left=observe first right ∧ observe second left=observe second right) := by
  constructor
  · intro same
    exact ⟨congrArg (observe first) same,congrArg (observe second) same⟩
  · rintro ⟨ha,hb⟩
    exact joint left right ha hb
#print axioms payload
#print axioms joint
#print axioms equal_iff
end R1Z.PV_RW_DataProduct
