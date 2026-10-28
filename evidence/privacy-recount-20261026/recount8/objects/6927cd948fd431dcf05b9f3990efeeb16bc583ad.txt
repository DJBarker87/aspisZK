import R1Z.PDict_Compare
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_Primitives
open Aeneas Aeneas.Std Result ProverRwFull

def sharedRef {T U : Type} (a : core.convert.AsRef T U) (x : T) : Result U :=
  a.as_ref x

def sliceRef {T : Type} (s : Slice T) : Result (Slice T) := .ok s

def invariant (pos block : Usize) : Result Bool := .ok (decide (pos < block))

variable [ExternalTypes]
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  { PDict_Compare.selected ops with
    op0 := @sharedRef, op1 := @sliceRef,
    op207 := .ok .Left, op210 := invariant, op221 := .ok () }

theorem op0_installed (ops : ExternalFuns) {T U : Type}
    (a : core.convert.AsRef T U) (x : T) :
    (selected ops).op0 a x = a.as_ref x := rfl

theorem op1_installed (ops : ExternalFuns) {T : Type} (s : Slice T) :
    (selected ops).op1 s = .ok s := rfl

theorem op207_installed (ops : ExternalFuns) :
    (selected ops).op207 = .ok digest.core_api.TruncSide.Left := rfl

theorem op210_installed (ops : ExternalFuns) (p b : Usize) :
    (selected ops).op210 p b = .ok (decide (p < b)) := rfl

theorem op221_installed (ops : ExternalFuns) :
    (selected ops).op221 = .ok () := rfl

#print axioms op0_installed
#print axioms op1_installed
#print axioms op207_installed
#print axioms op210_installed
#print axioms op221_installed
end R1Z.PDict_Primitives
