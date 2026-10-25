import Port1_CanonicalHeadline
import OraclePortHeadlineFrozen2PerAttempt
import Port1_CarrierObstruction
set_option autoImplicit false
noncomputable section
namespace AspisR1.Uni_CanonicalPerAttempt
attribute [local irreducible] CostedAllocationLedgerM10.fixed GSActualBankJobsM10.count
  GSBankOutputEnvelopeM10.candidates InitialPublicImageWorkM10.budget
open FS FS2 R0C.V3
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.OracleResampling
open OraclePortStoredExperimentC4 OraclePortFrozen2Consumer
open OraclePortRuntimeBindingC7 Port1_StoredCarrier
open OraclePortHeadlineFrozen2PerAttempt (Claims totalBound failureModel Qmax)

/-- The corrected byte-carrier endpoint retains the full repeated/adaptive
per-attempt bound. No unrestricted logical-input join is required. Physical,
raw canonical join and deployed runtime binding remain explicit obligations. -/
theorem final_soundness (D : LiteralByteProtocol.Decoder) (P : ByteProver) (Q : Nat)
    (hqueries : ∀ H : Bytes → State, (eval H P).1.length ≤ Q)
    (rust : Verifier) (runtime : Runtime) (physical : Physical rust)
    (raw : Port1_CanonicalJoin.AcceptedVerifierJoin D rust)
    (binding : StoredCarrierBinding D rust (lift P) runtime) :
    Claims D (lift P) Q runtime := by
  have join := Port1_CanonicalJoin.two_pass D rust physical raw
  have queries := Port1_CanonicalHeadline.lift_queries P Q hqueries
  have old := Port1_CanonicalHeadline.final_soundness D P Q hqueries rust runtime join binding
  have hb := Frozen2StartChargeProbability.failure_bound D (lift P) Q queries
  have hr := Port1_CanonicalHeadline.runtime_transport D rust P runtime join binding
  have ht : failureModel runtime ≤ totalBound Q := by
    apply (add_le_add (hr.trans hb) QueryScanModelFailure.exhaustion_bound).trans_eq
    unfold totalBound StartChargeNumeric.totalBound OracleDecisionPrereqNumeric.envelope
    ring
  exact ⟨old.1,old.2.1,old.2.2.1,ht,
    fun hQ => ht.trans (StartChargeNumeric.safe_range Q hQ)⟩

/-- Structural obstruction for ANY physical source that accepts at least once.
The independently chosen logical proof in L155 makes that old law false. -/
theorem no_global_join (D : LiteralByteProtocol.Decoder) (rust : Verifier)
    (physical : Physical rust) (H : Bytes → State) (i : Input)
    (accepted : (eval H (rust i)).2 = true) :
    ¬ OraclePortFrozen2Join.AcceptedVerifierJoin rust
      (verifier D OraclePortFrozen2.dV_frozen2) := by
  intro join
  let bad : Input := {i with proof := fun _ => i.proof 0}
  have same : rust bad = rust i := physical bad i rfl rfl
  have before : (eval H (rust bad)).2 = true := by rw [same]; exact accepted
  have joined := congrArg Prod.snd (join H bad before)
  have rejected := Port1_CarrierObstruction.constant_rejected D i.statement i.stored (i.proof 0) H
  change (eval H (rust bad)).2 =
    (eval H (verifier D OraclePortFrozen2.dV_frozen2
      ⟨i.statement,(fun _ => i.proof 0),i.stored⟩)).2 at joined
  rw [before,rejected] at joined
  cases joined

/-- The exact unconditional repeated/adaptive bound; no Q lower bound. -/
theorem failure_bound (D : LiteralByteProtocol.Decoder) (P : ByteProver) (Q : Nat)
    (hqueries : ∀ H : Bytes → State, (eval H P).1.length ≤ Q)
    (rust : Verifier) (runtime : Runtime) (physical : Physical rust)
    (raw : Port1_CanonicalJoin.AcceptedVerifierJoin D rust)
    (binding : StoredCarrierBinding D rust (lift P) runtime) :
    failureModel runtime ≤ ((Q+34 : Nat) : ℚ)*PerAttemptEnvelope.B +
      BinCombinedMerkleCollision.kappa (Q+1161) + 1/(2:ℚ)^126 + 1/(2:ℚ)^454 :=
  (final_soundness D P Q hqueries rust runtime physical raw binding).2.2.2.1

#print axioms final_soundness
#print axioms no_global_join
#print axioms failure_bound
#print final_soundness
end AspisR1.Uni_CanonicalPerAttempt
end
