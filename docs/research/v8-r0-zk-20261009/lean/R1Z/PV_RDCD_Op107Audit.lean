import R1Z.PV_CB_Op107Exact
import R1Z.PV_RDCD_OptionBinding
import R1Z.PV_RDCD_ShiftLiterals
import R1Z.PV_RDCD_Wrapping194
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RDCD_Op107Audit
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
/-- Replay of the unchanged retained importer at its original complete Result,
    Option and bijective raw carrier boundary. The supplemental source/adapter
    receipts establish deployed transport; no raw-output compilation is asserted. -/
theorem retained_importer (ops : ExternalFuns) (x : aspis_core.field.QM31) :
    (R1Z.PV_CB_Op107Exact.selected ops).op107 x = (do
      let value ← PV_CB_ShippedOp107.aspis_core.field.QM31.Insts.Aspis_coreR0ScalarCodeField.try_inv
        (R1Z.PV_CB_Op107Transport.encode x)
      ok (value.map R1Z.PV_CB_Op107Transport.decode)) :=
  R1Z.PV_CB_Op107Exact.op107_source ops x
#print axioms retained_importer
#print axioms PV_RDCD_OptionBinding.branch
#print axioms PV_RDCD_OptionBinding.residual
#print axioms PV_RDCD_Wrapping194.shr64_binding
#print axioms PV_RDCD_ShiftLiterals.shift31
#print axioms PV_RDCD_ShiftLiterals.shift1
end R1Z.PV_RDCD_Op107Audit
