import FIo_Install
import SAQ_RawWide
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

theorem m_add (x y : U32) :
    FIo_Native.aspis_core.field.M31.add x y=AspisR1CurrentWide.field.M31.add x y := rfl

theorem m_sub (x y : U32) :
    FIo_Native.aspis_core.field.M31.sub x y=AspisR1CurrentWide.field.M31.sub x y := rfl

theorem m_mul (x y : U32) :
    FIo_Native.aspis_core.field.M31.mul x y=AspisR1CurrentWide.field.M31.mul x y := rfl

#print axioms map_bind
#print axioms map_ok
#print axioms m_add
#print axioms m_sub
#print axioms m_mul
end AspisR1.FIo_FieldBridge
end
