import AspisRowStarts33
import Frozen2StartChargePrefix

/-! Per-step accounting, piece (c): the weighted start count of R1's charged
experiment (refines `Frozen2StartChargePrefix.starts`, `≤ Q + 34`).

Kind of result: a deterministic counting theorem about R1's charged
experiment for every oracle `H`. The adversary's starts are charged the
largest class cap `capMax`; the verifier's 33 rows are charged by
`AspisRowStarts.verifierCharge`. It concerns R1's 33-row protocol model;
the Aspis 40-row instance is not part of this file. -/
set_option autoImplicit false
noncomputable section
namespace AspisPerStep.ChargedWeight
open FS FS2 FS2.Duplex R0C.V3 AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open AspisR1 RecordedBinaryExperimentBin DecodedFirstReadUnionBound
open OraclePortStoredExperimentC4 OraclePortFrozen2Consumer Frozen2StartChargePrefix
open AspisPerStep.WeightedFirstRead AspisPerStep.RowStarts

/-- Piece (c): `decoderFirstWeight ≤ Q · capMax + verifierCharge` for the
charged experiment, under R1's hypothesis on the adversary's query count. -/
theorem charged_weight (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat)
    (hq : ∀ H : Bytes → State, (eval H P).1.length ≤ Q) (H : Bytes → State) :
    decoderFirstWeight dec wt emptyTable (eval H (charged D P)).1 ≤
      (Q : ℚ) * capMax + verifierCharge := by
  rw [charged_eval]
  unfold base
  rw [RawCutProverCompiler.experiment_eval, decoderFirstWeight_append]
  have hp := decoderFirstWeight_le_count_mul dec wt capMax wt_le_capMax
    emptyTable (eval H (prover P)).1
  have hc := DecoderQueryAccounting.starts_le_queries dec emptyTable (eval H (prover P)).1
  have hlen : (eval H (prover P)).1.length ≤ Q := by rw [prover_eval]; exact hq H
  have hcount : ((decoderFirstReads dec emptyTable (eval H (prover P)).1 : Nat) : ℚ) ≤ Q := by
    exact_mod_cast hc.trans hlen
  have hm := capMax_nonneg
  have hpq : (decoderFirstReads dec emptyTable (eval H (prover P)).1 : ℚ) * capMax ≤
      (Q : ℚ) * capMax := mul_le_mul_of_nonneg_right hcount hm
  exact add_le_add (hp.trans hpq) (verifier_weight D _ H _ _ _)

#print axioms charged_weight
end AspisPerStep.ChargedWeight
end
