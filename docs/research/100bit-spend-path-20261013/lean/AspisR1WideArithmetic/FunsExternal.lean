import AspisR1WideArithmetic.Types
import ExtractedCurrentQM31Mul
set_option autoImplicit false
namespace AspisR1WideArithmetic
open Aeneas Aeneas.Std Result
abbrev CurrentK := AspisR1Qm31ArithmeticProbe.field.QM31
abbrev CurrentC := AspisR1Qm31ArithmeticProbe.field.CM31

def toC (x : field.CM31) : CurrentC := ⟨x.a,x.b⟩
def fromC (x : CurrentC) : field.CM31 := ⟨x.a,x.b⟩
def toK (x : field.QM31) : CurrentK := ⟨toC x.c0,toC x.c1⟩
def fromK (x : CurrentK) : field.QM31 := ⟨fromC x.c0,fromC x.c1⟩

abbrev field.M31.add := AspisR1Qm31ArithmeticProbe.field.M31.add
abbrev field.M31.mul := AspisR1Qm31ArithmeticProbe.field.M31.mul

def field.CM31.add (x y : field.CM31) : Result field.CM31 := do
  let z ← AspisR1Qm31ArithmeticProbe.field.CM31.add (toC x) (toC y)
  .ok (fromC z)
def field.CM31.mul (x y : field.CM31) : Result field.CM31 := do
  let z ← AspisR1Qm31ArithmeticProbe.field.CM31.mul (toC x) (toC y)
  .ok (fromC z)
def field.QM31.add (x y : field.QM31) : Result field.QM31 := do
  let z ← AspisR1Qm31ArithmeticProbe.field.QM31.add (toK x) (toK y)
  .ok (fromK z)
def field.QM31.mul (x y : field.QM31) : Result field.QM31 := do
  let z ← AspisR1Qm31ArithmeticProbe.field.QM31.mul (toK x) (toK y)
  .ok (fromK z)

theorem to_fromK (x : CurrentK) : toK (fromK x)=x := rfl
theorem from_toK (x : field.QM31) : fromK (toK x)=x := rfl
#print axioms to_fromK
#print axioms from_toK
end AspisR1WideArithmetic
