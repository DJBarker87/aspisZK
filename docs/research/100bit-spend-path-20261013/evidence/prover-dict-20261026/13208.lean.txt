import R1Z.PDict_DigestNew
import R1Z.PDict_ErrorKind
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_DigestDelegates
open Aeneas Aeneas.Std Result ProverRwFull
section Source
variable [ExternalTypes]
def digestUpdate
  {D : Type} {T1 : Type} {Clause0_Clause1_OutputSize : Type}
  {Clause0_Clause1_Clause0_ArrayType : Type} (FixedOutputInst :
  digest.FixedOutput D Clause0_Clause1_OutputSize
  Clause0_Clause1_Clause0_ArrayType) (coredefaultDefaultInst :
  core.default.Default D) (UpdateInst : digest.Update D) (HashMarkerInst :
  digest.digest.HashMarker D) (coreconvertAsRefT1SliceU8Inst :
  core.convert.AsRef T1 (Slice Std.U8)) (self : D) (data : T1) :
  Result D
  := do
  let s ← coreconvertAsRefT1SliceU8Inst.as_ref data
  UpdateInst.update self s


end Source
abbrev native := PDict_Publication.native
@[reducible] def selected (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) : @ExternalFuns (native base) :=
  letI : ExternalTypes := native base
  { PDict_Publication.selected base ops with
    op2 := PDict_ErrorKind.eq
    op213 := digestUpdate
    op214 := PDict_DigestNew.digestNew }

theorem op2_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) (a b : core.io.error.ErrorKind) :
    (selected base ops).op2 a b = .ok (decide (a = b)) := PDict_ErrorKind.eq_exact a b

theorem op213_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op213 (native base) (selected base ops) =
      @digestUpdate (native base) := rfl

theorem op214_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op214 (native base) (selected base ops) =
      @PDict_DigestNew.digestNew (native base) := rfl

#print axioms op2_installed
#print axioms op213_installed
#print axioms op214_installed
end R1Z.PDict_DigestDelegates
