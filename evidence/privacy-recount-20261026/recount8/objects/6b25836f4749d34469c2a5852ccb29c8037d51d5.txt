import R1Z.PV_RunJoin_NativePublicReservation
set_option autoImplicit false
namespace R1Z.PV_RunJoin_PublicCarrierFrame
open Aeneas Aeneas.Std

/-- A carrier-level change to trace/semantic columns preserving the actual
compiled public statement. Compiler success/admission is not inferred. -/
def replaceColumns (i : PV_Src_NativeInput.Input)
    (other : PV_RunJoin_NominalCompiledData.SourceCompiled) : PV_Src_NativeInput.Input :=
  {i with compiled := {other with public_statement := i.compiled.public_statement}}

theorem public_unchanged (i : PV_Src_NativeInput.Input)
    (other : PV_RunJoin_NominalCompiledData.SourceCompiled) :
    PV_Src_NativeInput.publicInput (replaceColumns i other) = PV_Src_NativeInput.publicInput i := by
  cases i with
  | mk request witness change lane snapshot compiled => cases request <;> rfl

theorem native_public_unchanged (base : ProverRwFull.ExternalTypes)
    (i : PV_Src_NativeInput.Input) (other : PV_RunJoin_NominalCompiledData.SourceCompiled) :
    PV_RunJoin_NominalPublicData.fromInput base (replaceColumns i other) =
      PV_RunJoin_NominalPublicData.fromInput base i :=
  PV_RunJoin_NativePublicReservation.public_eq base _ _ (public_unchanged i other)

/-- The nominal map preserves all source information, including private trace
metadata; this is not identification with the independent arithmetic model. -/
theorem compiled_injective (base : ProverRwFull.ExternalTypes) :
    Function.Injective (PV_RunJoin_NominalCompiledData.compiled base) := by
  intro a b same
  have restored := congrArg (PV_RunJoin_NominalCompiledData.unCompiled base) same
  simpa only [PV_RunJoin_NominalCompiledData.compiled_roundtrip] using restored

#print axioms public_unchanged
#print axioms native_public_unchanged
#print axioms compiled_injective
end R1Z.PV_RunJoin_PublicCarrierFrame
