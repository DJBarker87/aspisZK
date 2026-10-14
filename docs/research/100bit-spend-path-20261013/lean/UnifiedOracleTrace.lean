import UnifiedOracleVerifier
import R1UnifiedVerifier
import R1UnifiedProtocol
import FS2.Theorem

/-! Trace decomposition for a verifier with a terminal oracle-reading decision. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.UnifiedOracleTrace

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisR1.TranscriptView

variable {M Cv W : Type} {L : Nat}

theorem trace_decomposition (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (decision : FS.Prefix (UnifiedSampler.Public L) (Message M) (Challenge Cv) →
      Message M → Program (Addr L) State Bool)
    (prover : Program (Addr L) State (UnifiedProtocol.Proof M))
    (H : Addr L → State) (pub : UnifiedSampler.Public L) :
    (eval H (FS2.experiment prover
      (UnifiedOracleVerifier.verifier p hD extract decision) pub)).1 =
      (eval H (FS2.experiment prover
        (UnifiedVerifier.verifier p hD extract (fun _ _ => true)) pub)).1 ++
      (eval H (decision
        ((UnifiedProtocol.protocol p hD extract).transcript H pub (eval H prover).2 33)
        ((UnifiedProtocol.protocol p hD extract).msg (eval H prover).2 33))).1 := by
  rw [FS2.experiment_eval, FS2.experiment_eval]
  rw [UnifiedOracleVerifier.verifier_eval]
  rw [UnifiedVerifier.verifier, FS2.verifier_eval]
  simp [UnifiedProtocol.protocol, List.append_assoc]

theorem result_eq_terminal (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (decision : FS.Prefix (UnifiedSampler.Public L) (Message M) (Challenge Cv) →
      Message M → Program (Addr L) State Bool)
    (prover : Program (Addr L) State (UnifiedProtocol.Proof M))
    (H : Addr L → State) (pub : UnifiedSampler.Public L) :
    (eval H (FS2.experiment prover
      (UnifiedOracleVerifier.verifier p hD extract decision) pub)).2.2 =
      (eval H (decision
        ((UnifiedProtocol.protocol p hD extract).transcript H pub (eval H prover).2 33)
        ((UnifiedProtocol.protocol p hD extract).msg (eval H prover).2 33))).2 := by
  rw [FS2.experiment_eval, UnifiedOracleVerifier.verifier_eval]

#print axioms trace_decomposition
#print axioms result_eq_terminal

end AspisR1.UnifiedOracleTrace
end
