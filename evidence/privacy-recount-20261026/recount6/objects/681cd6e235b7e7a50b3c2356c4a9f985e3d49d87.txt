import Std
set_option autoImplicit false
namespace R1Z.PV_RW_Outcome

-- A parameterized mirror of Result, including failure and divergence.
inductive Outcome (E A : Type) where
  | ok (value : A)
  | fail (error : E)
  | div

def bind {E A B : Type} (result : Outcome E A) (next : A → Outcome E B) : Outcome E B :=
  match result with
  | .ok value => next value
  | .fail error => .fail error
  | .div => .div

def map {E F A B : Type} (error : E → F) (value : A → B) : Outcome E A → Outcome F B
  | .ok a => .ok (value a)
  | .fail e => .fail (error e)
  | .div => .div

theorem ok_bind {E A B : Type} (a : A) (f : A → Outcome E B) : bind (.ok a) f=f a := rfl

theorem fail_bind {E A B : Type} (error : E) (f : A → Outcome E B) :
    bind (.fail error : Outcome E A) f=.fail error := rfl

theorem div_bind {E A B : Type} (f : A → Outcome E B) :
    bind (.div : Outcome E A) f=.div := rfl

theorem bind_ok {E A : Type} (result : Outcome E A) : bind result Outcome.ok=result := by
  cases result <;> rfl

theorem assoc {E A B C : Type} (result : Outcome E A)
    (f : A → Outcome E B) (g : B → Outcome E C) :
    bind (bind result f) g=bind result (fun a => bind (f a) g) := by
  cases result <;> rfl

theorem congr {E A B : Type} (result : Outcome E A) (left right : A → Outcome E B)
    (same : ∀ a, left a=right a) : bind result left=bind result right := by
  cases result with
  | ok a => exact same a
  | fail error => rfl
  | div => rfl

theorem map_id {E A : Type} (result : Outcome E A) : map id id result=result := by
  cases result <;> rfl

theorem map_comp {E F G A B C : Type} (ef : E → F) (fg : F → G) (ab : A → B) (bc : B → C)
    (result : Outcome E A) :
    map fg bc (map ef ab result)=map (fg∘ef) (bc∘ab) result := by
  cases result <;> rfl

theorem map_bind {E F A B C : Type} (error : E → F) (value : B → C)
    (result : Outcome E A) (f : A → Outcome E B) :
    map error value (bind result f)=
      bind (map error id result) (fun a => map error value (f a)) := by
  cases result <;> rfl
#print axioms ok_bind
#print axioms fail_bind
#print axioms div_bind
#print axioms bind_ok
#print axioms assoc
#print axioms congr
#print axioms map_id
#print axioms map_comp
#print axioms map_bind
end R1Z.PV_RW_Outcome
