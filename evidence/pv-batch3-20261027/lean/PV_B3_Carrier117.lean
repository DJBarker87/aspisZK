import R1Z.ProverRwFullExternalFuns
import PV_B3_Copy_117_Funs
import PV_B3_ArrayCarrier
namespace PV_B3_Carrier117
open Aeneas Aeneas.Std Result PV_B3_ArrayCarrier
set_option autoImplicit false
abbrev NativeQ := ProverRwFull.aspis_core.field.QM31
abbrev CopyQ := PV_B3_Copy_117.aspis_core.field.QM31
abbrev map := @resultMap

def toQ (q : CopyQ) : NativeQ := ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
def fromQ (q : NativeQ) : CopyQ := ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
def toArray {n : Usize} (a : Array CopyQ n) : Array NativeQ n := arrayMap toQ a
def fromArray {n : Usize} (a : Array NativeQ n) : Array CopyQ n := arrayMap fromQ a

theorem q_left (q : CopyQ) : fromQ (toQ q) = q := by
  cases q with | mk a b => cases a; cases b; rfl

theorem q_right (q : NativeQ) : toQ (fromQ q) = q := by
  cases q with | mk a b => cases a; cases b; rfl

theorem left {n : Usize} (a : Array CopyQ n) : fromArray (toArray a) = a :=
  inverse toQ fromQ q_left a

theorem right {n : Usize} (a : Array NativeQ n) : toArray (fromArray a) = a :=
  inverse fromQ toQ q_right a

theorem fail (e : Error) : map toQ (.fail e) = .fail e := rfl
theorem div : map toQ .div = .div := rfl

#print axioms q_left
#print axioms q_right
#print axioms left
#print axioms right
#print axioms fail
#print axioms div
end PV_B3_Carrier117
