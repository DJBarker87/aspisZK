import UnifiedOracleTotalCase
import R1UnifiedCollision
import R1CombinedMerkleCollision

/-! Existing Inj3 interface with a terminal oracle-reading decision program. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.UnifiedOracleInj

open FS FS2 FS2.Duplex R0C.V3
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisR1.TranscriptView

variable {M Cv W : Type} {L : Nat}

def inj (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (decision : UnifiedSampler.Prefix M Cv L → Message M → Program (Addr L) State Bool)
    (pub : UnifiedSampler.Public L)
    (prover : Program (Addr L) State (UnifiedProtocol.Proof M))
    (hpub : pub.pubBytes.length < 2^32)
    (hl : ∀ n < 33, p.lbl n = UnifiedLabels.label n)
    (m0 : M) (he0 : p.enc m0 = PublicInitFrame.emptyRecord)
    (Qtot : Nat)
    (hQ : ∀ H, FS2.distinctFirstReads
      (eval H (FS2.experiment prover
        (UnifiedOracleVerifier.verifier p hD extract decision) pub)) ≤ Qtot) :
    Inj3 (UnifiedProtocol.protocol p hD extract) (UnifiedDecoder.decode p hD pub)
      prover (fun x pf => UnifiedOracleVerifier.verifier p hD extract decision x pf)
      pub CombinedMerkleCollision.budget Qtot where
  Coll := CombinedMerkleCollision.Coll p Qtot
  mass := CombinedMerkleCollision.mass p Qtot prover
    (fun x pf => UnifiedOracleVerifier.verifier p hD extract decision x pf) pub hQ
  decodes := by
    intro H hc n a hn hfirst
    let v := eval H (FS2.experiment prover
      (UnifiedOracleVerifier.verifier p hD extract decision) pub)
    have holdCombined : ¬ CombinedMerkleCollision.Coll p Qtot v := by
      simpa [v] using hc
    have holdOld : ¬ UnifiedCollision.Coll p Qtot v := by
      intro hOld
      exact holdCombined (CombinedMerkleCollision.old_included p Qtot v hOld)
    obtain ⟨hold, htail⟩ := UnifiedCollision.outside p Qtot v holdOld
    have hπ : v.2.1 = (eval H prover).2 := by
      dsimp [v]
      rw [FS2.experiment_eval]
    rw [hπ] at hfirst ⊢
    have hQH : firstReads emptyTable v.1 ≤ Qtot := by
      simpa [v, FS2.distinctFirstReads] using hQ H
    exact UnifiedOracleTotalCase.decodes_and_follows p hD extract decision H pub prover
      hpub hl m0 he0 Qtot hQH hold htail n hn a hfirst

#print axioms inj

end AspisR1.UnifiedOracleInj
end
