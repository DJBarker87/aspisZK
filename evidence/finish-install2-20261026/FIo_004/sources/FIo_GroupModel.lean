import FIo_GroupFuns
import FIn_Polynomial
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIo_GroupModel
open Aeneas Aeneas.Std Result AspisR1Stage2.Stage2Finish
abbrev Ops := FIo_PairExtract.FIo_reference.Arithmetic Unit E

def arithmetic : Ops where
  coremarkerCopyInst := {cloneInst := {clone := fun x => ok x}}
  zero := ok FIn_Polynomial.zero
  add := FIn_Primitives.add
  mul := FIn_Polynomial.mul
  field := FIn_Primitives.field

/-- The owned reference uses the already installed actual arithmetic and reader. -/
def grouped := FIo_PairExtract.FIo_reference.grouped arithmetic

def subsetGo (ops : Ops) (low : Array E 16#usize) (mask : U16) :
    List (Usize × U32) → E → Result E
  | [],w => ok w
  | (i,b)::rest,w => do
    let challenge ← Array.index_usize low i
    let next ← FIo_PairExtract.FIo_reference.select_add ops w challenge mask b
    subsetGo ops low mask rest next

def contractGo (ops : Ops) (coefficients : Array E 12#usize) (low : Array E 16#usize) :
    List Usize → E → Result E
  | [],p => ok p
  | i::rest,p => do
    let mask ← Array.index_usize FIo_PairExtract.FIo_reference.MASKS i
    let weight ← FIo_PairExtract.FIo_reference.subset ops low mask
    let coefficient ← Array.index_usize coefficients i
    let product ← ops.mul coefficient weight
    let next ← ops.add p product
    contractGo ops coefficients low rest next

def coefficientGo (ops : Ops) (f : Slice U8) : List Usize → Array E 12#usize → Result (Array E 12#usize)
  | [],cs => ok cs
  | i::rest,cs => do
    let value ← ops.field f i
    let next ← FIo_PairExtract.FIo_reference.coefficient ops cs i value
    coefficientGo ops f rest next

theorem callbacks : arithmetic.zero=ok FIn_Polynomial.zero ∧
    arithmetic.add=FIn_Primitives.add ∧ arithmetic.mul=FIn_Polynomial.mul ∧
    arithmetic.field=FIn_Primitives.field := ⟨rfl,rfl,rfl,rfl⟩

#print axioms callbacks
end AspisR1.FIo_GroupModel
end
