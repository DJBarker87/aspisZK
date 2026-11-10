import AdapterRwTypes
import Stage2ContinuationTypes

/-! Shared names for identical Rust value carriers at independently extracted
boundaries. No operation or successful execution is supplied by this module. -/
namespace VTop_Stages
open Aeneas Aeneas.Std
abbrev aspis_core.field.M31 := AspisR1Stage2.aspis_core.field.M31
abbrev aspis_core.field.CM31 := AspisR1Stage2.aspis_core.field.CM31
abbrev aspis_core.field.QM31 := AspisR1Stage2.aspis_core.field.QM31
abbrev aspis_core.field.wide_exact.WideExact := AspisR1Stage2.aspis_core.field.wide_exact.WideExact
abbrev aspis_core.circle.SecureCirclePoint := AspisR1Stage2.aspis_core.circle.SecureCirclePoint
abbrev aspis_core.digest.Digest32 := AdapterRw.aspis_core.digest.Digest32
abbrev aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public :=
  AdapterRw.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public
abbrev verifier.Error := AdapterRw.aspis_r1_cost_probe.verifier.Error
abbrev verifier.Phase := AdapterRw.aspis_r1_cost_probe.verifier.Phase
abbrev transport.Variant := AspisR1Stage2.transport.Variant
abbrev verifier.Prepared := AspisR1Stage2.verifier.Prepared
abbrev verifier.Accumulator := AspisR1Stage2.verifier.Accumulator
abbrev verifier.BatchedWeights := AspisR1Stage2.verifier.BatchedWeights
abbrev verifier.QueryGeometry := AspisR1Stage2.verifier.QueryGeometry
abbrev verifier.View := AspisR1Stage2.verifier.View
end VTop_Stages
