import AspisRowStarts40
import AspisRec40ChargePrefix

/-! Weighted start count of the Aspis 40-row charged experiment
(refines `AspisRec40.ChargePrefix.starts`).

Kind of result: a deterministic counting theorem about the 40-row charged
experiment `AspisRec40.ChargePrefix.charged` for every oracle `H`. The
adversary's starts are charged the largest cap `capMax`; the verifier's 40
rows are charged by `AspisRowStarts40.verifierCharge40`
(= R1's `verifierCharge + capLambda + 6 * capRound`, `verifierCharge40_eq`).
It is not a hit-mass bound and not a probability statement. -/
set_option autoImplicit false
noncomputable section
namespace AspisPerStep.ChargedWeight40
open FS FS2 FS2.Duplex R0C.V3 AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open AspisR1 AspisR1.AspisLib.RecordedBinaryExperimentBin DecodedFirstReadUnionBound
open AspisPerStep.WeightedFirstRead AspisPerStep.RowStarts
open AspisCharge40 AspisRowStarts40
open OraclePortStoredExperimentC4 OraclePortStoredAdmissionC4

/-- `decoderFirstWeight ≤ Q · capMax + verifierCharge40` for the 40-row
charged experiment, under R1's hypothesis on the adversary's query count. -/
theorem charged_weight40 (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat)
    (hq : ∀ H : Bytes → State, (eval H P).1.length ≤ Q) (H : Bytes → State) :
    decoderFirstWeight AspisRows40.FinalStarts.decFinal charge40 emptyTable
      (eval H (AspisRec40.ChargePrefix.charged D P)).1 ≤
      (Q : ℚ) * capMax + verifierCharge40 := by
  rw [AspisRec40.ChargePrefix.charged_eval]
  unfold AspisRec40.ChargePrefix.base
  rw [RawCutProverCompiler.experiment_eval, decoderFirstWeight_append]
  have hp := decoderFirstWeight_le_count_mul AspisRows40.FinalStarts.decFinal charge40 capMax
    charge40_le_capMax emptyTable (eval H (AspisRec40.ChargePrefix.prover P)).1
  have hc := AspisR1.AspisLib.DecoderQueryAccounting.starts_le_queries AspisRows40.FinalStarts.decFinal
    emptyTable (eval H (AspisRec40.ChargePrefix.prover P)).1
  have hlen : (eval H (AspisRec40.ChargePrefix.prover P)).1.length ≤ Q := by
    rw [AspisRec40.ChargePrefix.prover_eval]; exact hq H
  have hcount : ((decoderFirstReads AspisRows40.FinalStarts.decFinal emptyTable
      (eval H (AspisRec40.ChargePrefix.prover P)).1 : Nat) : ℚ) ≤ Q := by
    exact_mod_cast hc.trans hlen
  have hpq : (decoderFirstReads AspisRows40.FinalStarts.decFinal emptyTable
      (eval H (AspisRec40.ChargePrefix.prover P)).1 : ℚ) * capMax ≤ (Q : ℚ) * capMax :=
    mul_le_mul_of_nonneg_right hcount capMax_nonneg
  exact add_le_add (hp.trans hpq) (verifier_weight40 D _ H _ _ _)

#print axioms charged_weight40
end AspisPerStep.ChargedWeight40
end
