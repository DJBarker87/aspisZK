import R1Z.PV_L2_Record

/-! Same failure-preserving writer, with value and events as separate
projections. This avoids kernel normalization of event append terms when
checking value erasure for long recorded operations. -/
set_option autoImplicit false
namespace R1Z.PV_L2_RecordCompact
open Aeneas Aeneas.Std Result R1Z.PV_L2_Record

def bind {α β : Type} (a : Recorded α) (f : α → Recorded β) : Recorded β where
  value := do let x ← a.value; (f x).value
  events := match a.value with
    | .fail _ | .div => a.events
    | .ok x => a.events ++ (f x).events

theorem bind_eq {α β : Type} (a : Recorded α) (f : α → Recorded β) :
    bind a f = PV_L2_Record.bind a f := by
  rcases a with ⟨value,events⟩
  cases value <;> rfl

local instance : Bind Recorded := ⟨@bind⟩

theorem bind_value {α β : Type} (a : Recorded α) (f : α → Recorded β) :
    (do let x ← a; f x).value = (do let x ← a.value; (f x).value) := rfl

theorem operation_bind_value {α β : Type} (event : Event) (result : Result α)
    (f : α → Recorded β) :
    (do let x ← operation event result; f x).value =
      (do let x ← result; (f x).value) := rfl

theorem fail_prefix {α β : Type} (error : Aeneas.Std.Error) (events : List Event)
    (f : α → Recorded β) : bind ⟨.fail error,events⟩ f = ⟨.fail error,events⟩ := rfl

theorem div_prefix {α β : Type} (events : List Event) (f : α → Recorded β) :
    bind ⟨.div,events⟩ f = ⟨.div,events⟩ := rfl

#print axioms bind_eq
#print axioms bind_value
#print axioms operation_bind_value
#print axioms fail_prefix
#print axioms div_prefix
end R1Z.PV_L2_RecordCompact
