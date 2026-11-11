import AspisChargedWeight40
import AspisRec40HitMass

/-! Item 14: composition of the per-step accounting for the Aspis 40-row
full experiment. For every decision `d` and the 40-row classifier
`classifier40 decodePair`, the prefix-hit mass of `AspisRec40.HitMass.projected
D d P` is at most `Q · capMax + verifierCharge40`.

Kind of result: a bound on the mass of the classifier's hit event in the
model experiment. It is not a bound on accepting a false statement: that also
needs the clean event, acceptance-to-checks and the extractor link, which are
open. No security figure follows from this theorem alone. -/
set_option autoImplicit false
noncomputable section
namespace AspisPerStep.ChargedHitMass40
open FS FS2 R0C.V3
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.CausalFirstHitUnionBound
open AspisR1 OraclePortStoredExperimentC4 OraclePortStoredAdmissionC4
open AspisPerStep.WeightedFirstRead AspisPerStep.RowStarts
open AspisCharge40 AspisRowStarts40 AspisPerStep.ChargedWeight40

theorem restricted_union_bound_weighted40 (decodePair : AspisAcceptance.Codec)
    (D : LiteralByteProtocol.Decoder) (d : Decision) (P : Prover) (Q : Nat)
    (hq : ∀ H : Bytes → State, (eval H P).1.length ≤ Q) :
    lazyMean (AspisRec40.HitMass.projected D d P) emptyTable
      (fun run => indicator (AspisRec40.HitMass.prefixHit (classifier40 decodePair) D P run)) ≤
      (Q : ℚ) * capMax + verifierCharge40 := by
  rw [AspisRec40.HitMass.hit_mass]
  apply weighted_decoded_first_read_bound AspisRows40.FinalStarts.decFinal
    (classifier40 decodePair) charge40 (AspisRec40.ChargePrefix.charged D P) emptyTable
  · exact decFinal_le_charge40 decodePair
  · apply weightedReadsBound_of_traces
    intro H
    exact charged_weight40 D P Q hq H

#print axioms restricted_union_bound_weighted40
end AspisPerStep.ChargedHitMass40
end
