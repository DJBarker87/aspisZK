import FIo_Install
import SAQ_RawWide
import FIo_ScalarBridge
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIo_FieldBridge
open Aeneas Aeneas.Std Result
abbrev NC := FIo_Native.aspis_core.field.CM31
abbrev NQ := FIo_Native.aspis_core.field.QM31
abbrev NE := FIo_Native.aspis_core.field.wide_exact.WideExact
abbrev CC := AspisR1CurrentWide.field.CM31
abbrev CQ := AspisR1CurrentWide.field.QM31
abbrev CE := AspisR1CurrentWide.field.wide_exact.WideExact

def cm (x : NC) : CC := ⟨x.a,x.b⟩
def qm (x : NQ) : CQ := ⟨cm x.c0,cm x.c1⟩
def wide (x : NE) : CE := ⟨qm x.c0,qm x.c1⟩
def map {A B : Type} (f : A → B) : Result A → Result B
  | .ok x => .ok (f x) | .fail e => .fail e | .div => .div

theorem map_bind {A B C : Type} (f : B → C) (x : Result A) (k : A → Result B) :
    map f (do let v ← x; k v) = (do let v ← x; map f (k v)) := by
  cases x <;> rfl

theorem map_ok {A B : Type} (f : A → B) (x : A) : map f (.ok x)=.ok (f x) := rfl

#print axioms map_bind
#print axioms map_ok
end AspisR1.FIo_FieldBridge
end
