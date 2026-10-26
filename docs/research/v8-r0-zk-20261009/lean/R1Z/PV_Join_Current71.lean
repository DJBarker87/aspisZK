import R1Z.ProverRwP6BodyData
import R1Z.PV_CB_Op71Exact
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_Current71
open Aeneas Aeneas.Std Result ProverRwFull PV_CB_Op71Transport

theorem scalar (bytes : Array U8 4#usize) :
    PV_CB_ShippedOp71.aspis_core.field.M31.from_le_bytes bytes =
      ProverRwSuccessParserSource.aspis_core.field.M31.from_le_bytes bytes := by
  unfold PV_CB_ShippedOp71.aspis_core.field.M31.from_le_bytes
    ProverRwSuccessParserSource.aspis_core.field.M31.from_le_bytes
    PV_CB_ShippedOp71.aspis_core.field.P
    ProverRwSuccessParserSource.aspis_core.field.P
    ProverRwDictionaryBytesSource.aspis_core.field.P
  rfl

/-- Structural Result/Option transport, including all short-input failures. -/
theorem complex (bytes : Slice U8) :
    (do let value ← PV_CB_ShippedOp71.aspis_core.field.CM31.from_le_bytes bytes
        ok (value.map decodeC)) =
      ProverRwSuccessParserSource.aspis_core.field.CM31.from_le_bytes bytes := by
  simp only [PV_CB_ShippedOp71.aspis_core.field.CM31.from_le_bytes,
    ProverRwSuccessParserSource.aspis_core.field.CM31.from_le_bytes,scalar,
    PV_CB_ShippedOp71.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
    PV_CB_ShippedOp71.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
    ProverRwDictionaryOptionSource.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
    ProverRwDictionaryOptionSource.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
    bind_assoc_eq,bind_tc_ok]
  repeat' first | rfl | (progress (congr 1)) | split
  all_goals simp only [bind_tc_ok,Option.map,decodeC]

theorem quartic (bytes : Slice U8) :
    (do let value ← PV_CB_ShippedOp71.aspis_core.field.QM31.from_le_bytes bytes
        ok (value.map decode)) =
      ProverRwSuccessParserSource.aspis_core.field.QM31.from_le_bytes bytes := by
  unfold PV_CB_ShippedOp71.aspis_core.field.QM31.from_le_bytes
    ProverRwSuccessParserSource.aspis_core.field.QM31.from_le_bytes
  rw [← complex,← complex]
  simp only [PV_CB_ShippedOp71.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
    PV_CB_ShippedOp71.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
    ProverRwDictionaryOptionSource.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
    ProverRwDictionaryOptionSource.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
    bind_assoc_eq,bind_tc_ok]
  repeat' first | rfl | (progress (congr 1)) | split
  all_goals simp only [bind_tc_ok,Option.map,decode]
variable [ExternalTypes]
theorem selected_bridge (ops : ExternalFuns) (bytes : Slice U8) :
    (ProverRwP6BodyStore.selected ops).op71 bytes = (PV_CB_Op71Exact.selected ops).op71 bytes := by
  change ProverRwSuccessParserSource.aspis_core.field.QM31.from_le_bytes bytes = _
  rw [PV_CB_Op71Exact.op71_source,quartic]
theorem op71_source (ops : ExternalFuns) (bytes : Slice U8) :
    (ProverRwP6BodyStore.selected ops).op71 bytes = (do
      let value ← PV_CB_ShippedOp71.aspis_core.field.QM31.from_le_bytes bytes
      ok (value.map decode)) :=
  (selected_bridge ops bytes).trans (PV_CB_Op71Exact.op71_source ops bytes)
#print axioms scalar
#print axioms complex
#print axioms quartic
#print axioms selected_bridge
#print axioms op71_source
end R1Z.PV_Join_Current71
