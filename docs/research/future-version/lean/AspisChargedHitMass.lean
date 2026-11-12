import AspisChargedWeight
import Frozen2StartChargeProbability
import AspisLib_Namespaces

/-! Per-step accounting, composition of (a), (b), (c) for R1's 33-row charged
experiment: the restricted classifier-hit mass is at most `Q · capMax +
verifierCharge` (refines `Frozen2StartChargeProbability.restricted_union_bound`,
`≤ (Q+34) · B`).

Kind of result: a probability theorem about R1's charged experiment and
classifier. It is NOT a statement about Aspis and does not restate or tighten
R1's claim (R1's numeric total is unchanged; whether R1 adopts this is a
separate decision). It is the template the Aspis 40-row instance must
reproduce. -/
set_option autoImplicit false
noncomputable section
namespace AspisPerStep.ChargedHitMass
open FS FS2 R0C.V3
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.CausalFirstHitUnionBound
open AspisR1 OraclePortStoredExperimentC4 OraclePortFrozen2Consumer
open RawRecordedOracleExtractionMassBin Frozen2StartChargePrefix Frozen2StartChargeClean
open AspisPerStep.WeightedFirstRead AspisPerStep.RowCharge AspisPerStep.RowStarts
  AspisPerStep.ChargedWeight

theorem restricted_union_bound_weighted (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat)
    (hq : ∀ H : Bytes → State, (eval H P).1.length ≤ Q) :
    lazyMean (projected D P) emptyTable (fun run => indicator (prefixHit D P run)) ≤
      (Q : ℚ) * capMax + verifierCharge := by
  rw [Frozen2StartChargeProbability.hit_mass]
  apply weighted_decoded_first_read_bound
    (RawAdaptiveLiteralDecoder.decode RawFullPublicSelection.select LiteralTableWordChoiceBin.choose)
    RawAdaptiveClassifierHitDensity.classifier wt (charged D P) emptyTable
  · exact adaptive_decoded_classifier_le_charge RawFullPublicSelection.select
      LiteralTableWordChoiceBin.choose
  · apply weightedReadsBound_of_traces
    intro H
    exact charged_weight D P Q hq H

#print axioms restricted_union_bound_weighted
end AspisPerStep.ChargedHitMass
end
