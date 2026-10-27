import R1Z.PV_CB_CandidateDictionary
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_CandidateDictionary
open Aeneas Aeneas.Std Result ProverRwFull
theorem op71 (base : ExternalTypes) (ops : @ExternalFuns (native base)) (bytes : Slice U8) :
    (selected base ops).op71 bytes = (do
      let value ← PV_CB_ShippedOp71.aspis_core.field.QM31.from_le_bytes bytes
      ok (value.map PV_CB_Op71Transport.decode)) := by
  letI : ExternalTypes := native base
  change (PV_CB_Op71Exact.selected ops).op71 bytes = _
  exact R1Z.PV_CB_Op71Exact.op71_source ops bytes
#print axioms op71
theorem op72 (base : ExternalTypes) (ops : @ExternalFuns (native base)) (x : aspis_core.field.QM31) (bytes : Slice U8) :
    (selected base ops).op72 x bytes =
      PV_CB_ShippedOp72.aspis_core.field.QM31.write_le_bytes (PV_CB_Op72Transport.encode x) bytes := by
  letI : ExternalTypes := native base
  change (PV_CB_Op72Exact.selected ops).op72 x bytes = _
  exact R1Z.PV_CB_Op72Exact.op72_source ops x bytes
#print axioms op72
theorem op80 (base : ExternalTypes) (ops : @ExternalFuns (native base)) {E : Type}
    (inst : aspis_core.r0.scalar.CodeField E) (x y : E) (h : Array E 4#usize) :
    (selected base ops).op80 inst x y h =
      PV_CB_ShippedOp80.aspis_core.r0.fold.phi_inverse (PV_CB_Op80Transport.encode inst) x y h := by
  letI : ExternalTypes := native base
  change (PV_CB_Op80Exact.selected ops).op80 inst x y h = _
  exact R1Z.PV_CB_Op80Exact.op80_source ops inst x y h
#print axioms op80
end R1Z.PV_CB_CandidateDictionary
