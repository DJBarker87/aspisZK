-- PCWT_ binding discharge for AspisR1WeightsFieldCurrent.weights.field (module WeightsFieldExplicitDecoder), route (b).
-- What was bound: the fresh weights::field text (PCQF_E006, frozen 4bb3b3f, overflow ON) has two external axioms,
-- aspis_core::field::wide_exact::WideExact (type) and WideExact::from_le_bytes (crates/aspis-core/src/field/wide_exact.rs 255:4-270:5).
-- PRVD.Eq.weights.field (P3d) is stated for every W and d.  Here W is instantiated at the gate WideExact of module
-- R1CandidateWideParserSource and d at the FRESH frozen from_le_bytes (NMH_wide_decode emission, no external), whose
-- fresh = gate equality is PRVEq.R1CandidateWideParserSource_k1 (EQUALITY_PROVED, PCVH_L008).
-- Result: the fresh weights::field with from_le_bytes not externalised equals the gate weights.field at the gate decoder.
import Aeneas
import WeightsFieldExplicitDecoder
import PRVEq_WeightsFieldExplicitDecoder_P3d
import PRVEq_PCVH_R1CandidateWideParserSource_k1
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

theorem PRVEq.WeightsFieldExplicitDecoder_t1.weights.field_frozen_decoder :
    @AspisR1WeightsFieldCurrent.PRVFresh_WeightsFieldExplicitDecoder.weights.field
      AspisR1CandidateParser.field.wide_exact.WideExact
      AspisR1CandidateParser.PRVFresh_R1CandidateWideParserSource_j1.field.wide_exact.WideExact.from_le_bytes =
    @AspisR1WeightsFieldCurrent.weights.field
      AspisR1CandidateParser.field.wide_exact.WideExact
      AspisR1CandidateParser.field.wide_exact.WideExact.from_le_bytes := by
  rw [PRVEq.R1CandidateWideParserSource_k1.field.wide_exact.WideExact.from_le_bytes]
  exact PRVD.Eq.weights.field _
#print axioms PRVEq.WeightsFieldExplicitDecoder_t1.weights.field_frozen_decoder
