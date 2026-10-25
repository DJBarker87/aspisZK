import WAdm_Fissioned.TypesExternal
open Aeneas Aeneas.Std
namespace WAdm_Fissioned
abbrev aspis_core.field.M31 := OraclePortCkptAbi2Extracted.aspis_core.field.M31
abbrev aspis_core.field.CM31 := OraclePortCkptAbi2Extracted.aspis_core.field.CM31
abbrev aspis_core.field.QM31 := OraclePortCkptAbi2Extracted.aspis_core.field.QM31
abbrev aspis_core.circle.SecureCirclePoint := OraclePortCkptAbi2Extracted.aspis_core.circle.SecureCirclePoint
abbrev aspis_core.field.wide_exact.WideExact := OraclePortCkptAbi2Extracted.aspis_core.field.wide_exact.WideExact
abbrev aspis_core.digest.Digest32 := AspisR1Stage2.aspis_core.digest.Digest32
abbrev aspis_r1_cost_probe.transport.Variant := OraclePortCkptAbi2Extracted.aspis_r1_cost_probe.transport.CheckpointAbi2Variant
abbrev aspis_r1_cost_probe.verifier.Prepared := OraclePortCkptAbi2Extracted.aspis_r1_cost_probe.verifier.Prepared
/-- Verbatim emitted fields; native structs are nominal aliases above. -/
structure WAdm_model.WAdm_Fields where
  roots : Array (Array Std.U8 32#usize) 2#usize
  state : Array Std.U8 32#usize
  early : Array aspis_core.field.wide_exact.WideExact 4#usize
  rho : aspis_core.field.QM31
  queries : Array Std.U32 22#usize
  semantic : Array aspis_core.field.QM31 10#usize
  coordinates : Array aspis_core.field.QM31 4#usize
  tail : Array aspis_core.field.wide_exact.WideExact 2#usize
  power : aspis_core.field.QM31
end WAdm_Fissioned
