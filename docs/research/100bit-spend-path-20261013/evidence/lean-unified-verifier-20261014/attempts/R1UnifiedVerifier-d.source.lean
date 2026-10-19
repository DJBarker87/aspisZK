import R1UnifiedProtocol
import FS.LemmaB

/-! The generic FS2 verifier run for the unified sampler protocol, together
with trace inclusion and consistency. The extractor and decision procedure
remain explicit; these are trace facts only. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.UnifiedVerifier

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisR1.TranscriptView

variable {M Cv : Type} {L : Nat}

def verifier {W : Type} (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (decision : FS.Prefix (UnifiedSampler.Public L) (Message M) (Challenge Cv) → Message M → Bool)
    (pub : UnifiedSampler.Public L) (π : UnifiedProtocol.Proof M) :
    Program (Addr L) State Bool :=
  FS2.verifier (UnifiedProtocol.protocol p hD extract) decision pub π

theorem reads {W : Type} (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (decision : FS.Prefix (UnifiedSampler.Public L) (Message M) (Challenge Cv) → Message M → Bool)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (π : UnifiedProtocol.Proof M) (i : Nat) (hi : i < 33) (a : Addr L)
    (ha : a ∈ (eval H (UnifiedSampler.samp p hD i
      (UnifiedRun.transcript p hD H pub π.1 π.2 i)
      (UnifiedRun.message π.1 π.2 i)).toProgram).1.map Prod.fst) :
    a ∈ (eval H (verifier p hD extract decision pub π)).1.map Prod.fst := by
  apply FS2.verifier_reads (UnifiedProtocol.protocol p hD extract)
    decision H pub π i hi a
  rw [← UnifiedProtocol.chain_eq p hD extract H pub π i] at ha
  exact ha

theorem trace_consistent {W : Type} (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (decision : FS.Prefix (UnifiedSampler.Public L) (Message M) (Challenge Cv) → Message M → Bool)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (π : UnifiedProtocol.Proof M) :
    ∀ q ∈ (eval H (verifier p hD extract decision pub π)).1,
      q.2 = H q.1 := by
  exact FS.eval_consistent H _

#print axioms reads
#print axioms trace_consistent

end AspisR1.UnifiedVerifier
end
