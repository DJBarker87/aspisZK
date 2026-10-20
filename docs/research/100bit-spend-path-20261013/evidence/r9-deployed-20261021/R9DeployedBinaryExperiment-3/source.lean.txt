import RecordedBinaryExperimentBin
import R9TwoTransactionExperiment

/-! Binary-extractor version of R9's explicit two-transaction experiment.
Checkpoint bytes pass unchanged to the Pool continuation. This is an abstract
caller model: persistence does not identify the continuation with frozen Rust. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.R9DeployedBinaryExperiment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.CausalFirstHitUnionBound AspisV8R19.OracleResampling
open FS FS2 RawCutTranscriptRun
open RawCutProverCompiler RecordedBinaryExperimentBin
open R9TwoTransactionExperiment
attribute [local instance] Classical.propDecidable

abbrev Tx1 := Program Bytes State (First Bytes)
abbrev PoolTx2 := Bytes → Program Bytes State Run

/-- tx1 writes its checkpoint; Pool invokes nested tx2 with those same bytes.
Both transactions share the oracle, including adversarial prior queries. -/
def deployed (tx1 : Tx1) (poolTx2 : PoolTx2) :=
  R9TwoTransactionExperiment.experiment tx1 poolTx2

def failure (v : View Bytes State (Outcome Bytes))
    (coins : GSConcreteByteDecoderBank.RawCoins) : Prop :=
  ∃ run, v.2.resumed = some run ∧ run.2.2 = true ∧
    RawRecordedPublicSpendExtractorBin.extract run coins = none

def mass (v : View Bytes State (Outcome Bytes)) : ℚ :=
  mean (fun coins => indicator (failure v coins))

/-- Probability of acceptance and failure of the actual binary extractor;
private extractor coins are averaged independently inside the oracle mean. -/
def deployedFailureModel (tx1 : Tx1) (poolTx2 : PoolTx2) : ℚ :=
  lazyMean (deployed tx1 poolTx2) emptyTable mass

/-- This pointwise same-statement/caller law is NOT a consequence of P2'. -/
def CallerReachability (tx1 : Tx1) (poolTx2 : PoolTx2)
    (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) : Prop :=
  ∀ H run, (eval H (deployed tx1 poolTx2)).2.resumed = some run →
    run.2.2 = true → run = eval H (recorded D d P)

/-- R9's preferred off-scan ordered refinement plus error propagation,
spelled independently of its historical clean-model extractor. -/
theorem caller_of_ordered_rejects (tx1 : Tx1) (poolTx2 : PoolTx2)
    (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover)
    (ordered : OrderedSourceRefinement (deployed tx1 poolTx2) (recorded D d P))
    (rejects : ∀ H, abort (eval H (deployed tx1 poolTx2)) →
      ∀ run, (eval H (deployed tx1 poolTx2)).2.resumed = some run →
        run.2.2 ≠ true) : CallerReachability tx1 poolTx2 D d P := by
  intro H run hr ha
  by_cases hab : abort (eval H (deployed tx1 poolTx2))
  · exact False.elim (rejects H hab run hr ha)
  · exact ordered H hab run hr

/-- Finite-support shared-oracle probability law, without a fresh-scan or
independence assumption on the adversary's oracle addresses. -/
theorem transport_no_scan_charge (tx1 : Tx1) (poolTx2 : PoolTx2)
    (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover)
    (caller : CallerReachability tx1 poolTx2 D d P) :
    deployedFailureModel tx1 poolTx2 ≤
      lazyMean (recorded D d P) emptyTable RawRecordedOracleExtractionMassBin.failureMass := by
  apply OracleProgramLawExt.lazyMean_le_of_eval
  intro H
  apply mean_mono
  intro coins
  apply indicator_mono
  rintro ⟨run, hr, ha, hf⟩
  have he := caller H run hr ha
  exact ⟨by simpa only [← he] using ha, by simpa only [← he] using hf⟩

/-- Exactly one existing query-scan allowance. Scan rejection actually proves
the stronger zero-charge result; no uniform-word probability is postulated. -/
theorem transport (tx1 : Tx1) (poolTx2 : PoolTx2)
    (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover)
    (caller : CallerReachability tx1 poolTx2 D d P) :
    DeployedTransport D d P (deployedFailureModel tx1 poolTx2) := by
  have hn : 0 ≤ QueryScanModelFailure.failureProbability (2^18) := by
    unfold QueryScanModelFailure.failureProbability
    positivity
  exact (transport_no_scan_charge tx1 poolTx2 D d P caller).trans
    (le_add_of_nonneg_right hn)

/-- Concrete witness that exact checkpoint persistence constrains no resumed
public, proof, log or verdict in the absence of a caller/decoder law. -/
theorem arbitrary_resume (checkpoint : Bytes) (words : WordTape) (run : Run)
    (H : Bytes → State) :
    eval H (deployed (.done ⟨some checkpoint, words⟩) (fun _ => .done run)) =
      ([], ⟨⟨some checkpoint, words⟩, some run⟩) := by
  exact R9TwoTransactionExperiment.eval_success _ _ H checkpoint rfl

#print axioms caller_of_ordered_rejects
#print axioms transport_no_scan_charge
#print axioms transport
#print axioms arbitrary_resume
end AspisR1.R9DeployedBinaryExperiment
end
