import R1Z.PV_CB_CandidateDictionary
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_CandidateDictionary
open Aeneas Aeneas.Std Result ProverRwFull
theorem op100 (base : ExternalTypes) (ops : @ExternalFuns (native base)) (x : aspis_core.field.wide_exact.WideExact) :
    (selected base ops).op100 x = (do
      let y ← PV_CB_ShippedOp100.aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.neg (PV_CB_Op100Transport.encodeW x)
      ok (PV_CB_Op100Transport.decodeW y)) := by
  change (PV_CB_Op100Exact.selected ops).op100 x = _
  exact R1Z.PV_CB_Op100Exact.op100_source ops x
#print axioms op100
theorem op101 (base : ExternalTypes) (ops : @ExternalFuns (native base)) (x : aspis_core.field.QM31) :
    (selected base ops).op101 x = (do
      let y ← PV_CB_ShippedOp101.aspis_core.field.QM31.Insts.Aspis_coreR0ScalarCodeField.neg (PV_CB_Op101Transport.encode x)
      ok (PV_CB_Op101Transport.decode y)) := by
  change (PV_CB_Op101Exact.selected ops).op101 x = _
  exact R1Z.PV_CB_Op101Exact.op101_source ops x
#print axioms op101
theorem op105 (base : ExternalTypes) (ops : @ExternalFuns (native base)) (x : aspis_core.field.M31) :
    (selected base ops).op105 x =
      PV_CB_ShippedOp105.aspis_core.field.M31.Insts.Aspis_coreR0ScalarCodeField.try_inv x := by
  change (PV_CB_Op105Exact.selected ops).op105 x = _
  exact R1Z.PV_CB_Op105Exact.op105_source ops x
#print axioms op105
theorem op107 (base : ExternalTypes) (ops : @ExternalFuns (native base)) (x : aspis_core.field.QM31) :
    (selected base ops).op107 x = (do
      let value ← PV_CB_ShippedOp107.aspis_core.field.QM31.Insts.Aspis_coreR0ScalarCodeField.try_inv (PV_CB_Op107Transport.encode x)
      ok (value.map PV_CB_Op107Transport.decode)) := by
  change (PV_CB_Op107Exact.selected ops).op107 x = _
  exact R1Z.PV_CB_Op107Exact.op107_source ops x
#print axioms op107
theorem op110 (base : ExternalTypes) (ops : @ExternalFuns (native base)) (x : aspis_core.field.M31) :
    (selected base ops).op110 x =
      PV_CB_ShippedOp110.aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31 x := by
  change (PV_CB_Op110Source.selected ops).op110 x = _
  exact R1Z.PV_CB_Op110Source.op110_source ops x
#print axioms op110
theorem op111 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    (selected base ops).op111 = .ok PV_CB_ShippedOp111.aspis_core.state_only_hiding.PINNED_POOL_V1_PAYMENT_RELATION_FREE_MASK_FINGERPRINT := by
  change (PV_CB_State.selected ops).op111 = _
  exact R1Z.PV_CB_Op111Source.op111_source ops
#print axioms op111
theorem op114 (base : ExternalTypes) (ops : @ExternalFuns (native base)) (a b : aspis_core.state_only_hiding.StateOnlyHidingContext) :
    (selected base ops).op114 a b =
      PV_CB_ShippedOp114.aspis_core.state_only_hiding.StateOnlyHidingContext.Insts.CoreCmpPartialEqStateOnlyHidingContext.eq a b := by
  change (PV_CB_Op114Source.selected ops).op114 a b = _
  exact R1Z.PV_CB_Op114Source.op114_source ops a b
#print axioms op114
end R1Z.PV_CB_CandidateDictionary
