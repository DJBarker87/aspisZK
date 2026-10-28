import R1Z.PV_RunJoin_NativeSelectedInputs
import R1Z.PV_CB3_Op51Source
import R1Z.PV_CB3_Op120Source
import R1Z.PV_CB3_Op246Source
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CallbackInstallation
open Aeneas Aeneas.Std Result ProverRwFull

/-- Install three independently checked complete source/reference equations
on the SAME nominal input dictionary. Other callback fields remain explicit;
this construction is not the missing complete extracted-trace refinement. -/
@[reducible] def selected (base : ExternalTypes)
    (ops : @ExternalFuns (PDict_CodecDictionary.native base)) :
    @ExternalFuns (PDict_CodecDictionary.native base) :=
  letI : ExternalTypes := PDict_CodecDictionary.native base
  PV_CB3_Op51Source.selected
    (PV_CB3_Op120Source.selected (ProverRwSuccessHashes.selected ops))

/-- This is the exact dictionary used by NativeSelectedInputs.ledgerInputs,
including its outer codec installation, rather than another convenient copy. -/
@[reducible] def installed (base : ExternalTypes)
    (ops : @ExternalFuns (PDict_CodecDictionary.native base)) :
    @ExternalFuns (PDict_CodecDictionary.native base) :=
  PDict_CodecDictionary.selected base (selected base ops)

theorem op51_source (base : ExternalTypes)
    (ops : @ExternalFuns (PDict_CodecDictionary.native base))
    (x : aspis_core.field.wide_exact.WideExact) :
    letI : ExternalTypes := PDict_CodecDictionary.native base
    (installed base ops).op51 x = PV_CB3_Op51Source.Raw.wide_bytes_flat x := by
  letI : ExternalTypes := PDict_CodecDictionary.native base
  rw [PDict_CodecDictionary.op51_retained]
  exact PV_CB3_Op51Source.op51_source
    (PV_CB3_Op120Source.selected (ProverRwSuccessHashes.selected ops)) x

theorem op120_source (base : ExternalTypes)
    (ops : @ExternalFuns (PDict_CodecDictionary.native base))
    (p : Array aspis_core.field.QM31 28#usize) :
    letI : ExternalTypes := PDict_CodecDictionary.native base
    (installed base ops).op120 p = PV_CB3_Op120Source.Raw.boundary_flat p := by
  letI : ExternalTypes := PDict_CodecDictionary.native base
  exact PV_CB3_Op120Source.op120_source (ProverRwSuccessHashes.selected ops) p

theorem op246_source (base : ExternalTypes)
    (ops : @ExternalFuns (PDict_CodecDictionary.native base)) {H : Type}
    (inst : aspis_core.digest.Digest32 H) (hash : H)
    (left right : Array U8 32#usize) :
    letI : ExternalTypes := PDict_CodecDictionary.native base
    (installed base ops).op246 inst hash left right =
      PV_CB3_ShippedOp246.multiproof.binary_parent inst hash left right := by
  letI : ExternalTypes := PDict_CodecDictionary.native base
  exact PV_CB3_Op246Source.op246_source ops inst hash left right

theorem map_error (base : ExternalTypes)
    (ops : @ExternalFuns (PDict_CodecDictionary.native base)) :
    @PV_RunJoin_MapErrInstalled.Identity (PDict_CodecDictionary.native base) (installed base ops) :=
  PV_RunJoin_DictionaryIdentity.map_error base (selected base ops)

#print axioms op51_source
#print axioms op120_source
#print axioms op246_source
#print axioms map_error
end R1Z.PV_RunJoin_CallbackInstallation
