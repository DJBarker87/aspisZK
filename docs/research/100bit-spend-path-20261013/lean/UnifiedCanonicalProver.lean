import R1UnifiedPayloadZero
import R1PublicInitFrame

/-! A prover wrapper fixes the unused zero payload field while preserving the
oracle trace of the original prover and verifier. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.UnifiedCanonicalProver

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.SourceDuplexStep

variable {M Cv : Type} {L : Nat}

def prover (m0 : M) (P : Program (Addr L) State (UnifiedProtocol.Proof M)) :
    Program (Addr L) State (UnifiedProtocol.Proof M) :=
  bind P (fun π => Program.done (UnifiedPayloadZero.proof m0 π))

theorem eval_prover (H : Addr L → State) (m0 : M)
    (P : Program (Addr L) State (UnifiedProtocol.Proof M)) :
    eval H (prover m0 P) =
      ((eval H P).1, UnifiedPayloadZero.proof m0 (eval H P).2) := by
  unfold prover
  rw [eval_bind]
  simp [eval]

theorem codec (p : Params M Cv L) (H : Addr L → State) (m0 : M)
    (P : Program (Addr L) State (UnifiedProtocol.Proof M))
    (he : p.enc m0 = PublicInitFrame.emptyRecord) :
    p.enc ((eval H (prover m0 P)).2.2 0) = PublicInitFrame.emptyRecord := by
  rw [eval_prover]
  exact he

theorem experiment_trace_eq {W : Type} (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (decision : FS.Prefix (UnifiedSampler.Public L)
      (TranscriptView.Message M) (TranscriptView.Challenge Cv) →
      TranscriptView.Message M → Bool)
    (pub : UnifiedSampler.Public L) (H : Addr L → State) (m0 : M)
    (P : Program (Addr L) State (UnifiedProtocol.Proof M)) :
    (eval H (FS2.experiment (prover m0 P)
      (fun x π => UnifiedVerifier.verifier p hD extract decision x π) pub)).1 =
    (eval H (FS2.experiment P
      (fun x π => UnifiedVerifier.verifier p hD extract decision x π) pub)).1 := by
  rw [FS2.experiment_eval, FS2.experiment_eval, eval_prover]
  simp only [UnifiedPayloadZero.proof]
  congr 1

#print axioms eval_prover
#print axioms codec
#print axioms experiment_trace_eq

end AspisR1.UnifiedCanonicalProver
end
