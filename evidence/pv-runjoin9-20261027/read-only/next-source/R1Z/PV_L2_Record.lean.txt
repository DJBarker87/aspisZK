import R1Z.CertCheckBase

/-! A failure-preserving writer for recorded Aeneas operations. No result is
assumed successful, and events before fail/div remain in the prefix. -/
set_option autoImplicit false
namespace R1Z.PV_L2_Record
open Aeneas Aeneas.Std Result

inductive Event where
  | guard (site : Nat) (index bound : Nat) (result : Bool)
  | index (array : Nat) (offset : Nat)
  | mul (left right : Nat)
  | rem (left right : Nat)
  | add (left right : Nat)
  deriving DecidableEq

structure Recorded (α : Type) where
  value : Result α
  events : List Event

def pure {α : Type} (a : α) : Recorded α := ⟨ok a,[]⟩
def bind {α β : Type} (a : Recorded α) (f : α → Recorded β) : Recorded β :=
  match a.value with
  | .fail e => ⟨.fail e,a.events⟩
  | .div => ⟨.div,a.events⟩
  | .ok value => let rest := f value; ⟨rest.value,a.events ++ rest.events⟩
instance : Pure Recorded := ⟨@pure⟩
instance : Bind Recorded := ⟨@bind⟩

def operation {α : Type} (e : Event) (result : Result α) : Recorded α := ⟨result,[e]⟩

theorem bind_value {α β : Type} (a : Recorded α) (f : α → Recorded β) :
    (bind a f).value = (do let value ← a.value; (f value).value) := by
  rcases a with ⟨value, events⟩
  cases value <;> rfl

theorem operation_value {α : Type} (e : Event) (result : Result α) :
    (operation e result).value = result := rfl

theorem fail_prefix {α β : Type} (e : Aeneas.Std.Error) (events : List Event)
    (f : α → Recorded β) : bind ⟨.fail e,events⟩ f = ⟨.fail e,events⟩ := rfl

theorem div_prefix {α β : Type} (events : List Event) (f : α → Recorded β) :
    bind ⟨.div,events⟩ f = ⟨.div,events⟩ := rfl

theorem operation_bind_value {α β : Type} (event : Event) (result : Result α)
    (f : α → Recorded β) :
    (do let a ← operation event result; f a).value = (do let a ← result; (f a).value) :=
  bind_value (operation event result) f

theorem pure_value {α : Type} (a : α) : (pure a).value = ok a := rfl

#print axioms operation_bind_value
#print axioms pure_value

#print axioms bind_value
#print axioms operation_value
#print axioms fail_prefix
#print axioms div_prefix
end R1Z.PV_L2_Record
