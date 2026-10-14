import R1UnifiedTotalCase
import R1UnifiedCollision

/-! The complete unified decoder supplies the existing v3 injection interface.
Both collision events are charged on the original prover experiment. The
empty row-zero encoding is a fixed codec property, not a prover restriction. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.UnifiedInj

open FS FS2 FS2.Duplex R0C.V3
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisR1.TranscriptView

variable {M Cv W : Type} {L : Nat}

def inj (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (decision : UnifiedSampler.Prefix M Cv L → Message M → Bool)
    (pub : UnifiedSampler.Public L)
    (prover : Program (Addr L) State (UnifiedProtocol.Proof M))
    (hpub : pub.pubBytes.length < 2^32)
    (hl : ∀ n < 33, p.lbl n = UnifiedLabels.label n)
    (m0 : M) (he0 : p.enc m0 = PublicInitFrame.emptyRecord)
    (Qtot : Nat)
    (hQ : ∀ H, FS2.distinctFirstReads
      (eval H (FS2.experiment prover
        (fun x pf => UnifiedVerifier.verifier p hD extract decision x pf) pub)) ≤ Qtot) :
    Inj3 (UnifiedProtocol.protocol p hD extract) (UnifiedDecoder.decode p hD pub)
      prover (fun x pf => UnifiedVerifier.verifier p hD extract decision x pf)
      pub UnifiedCollision.budget Qtot where
  Coll := UnifiedCollision.Coll p Qtot
  mass := UnifiedCollision.mass p Qtot prover
    (fun x pf => UnifiedVerifier.verifier p hD extract decision x pf) pub hQ
  decodes := by
    intro H hc n a hn hfirst
    obtain ⟨hold, htail⟩ := UnifiedCollision.outside p Qtot _ hc
    have hπ : (eval H (FS2.experiment prover
        (fun x pf => UnifiedVerifier.verifier p hD extract decision x pf) pub)).2.1 =
        (eval H prover).2 := by rw [FS2.experiment_eval]
    rw [hπ] at hfirst ⊢
    exact UnifiedTotalCase.decodes_and_follows p hD extract decision H pub prover
      hpub hl m0 he0 Qtot (hQ H) hold htail n hn a hfirst

#print axioms inj

end AspisR1.UnifiedInj
end
