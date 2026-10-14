import R1UnifiedInj
import R1UnifiedChainDensity
import R1UnifiedFramework

/-! Conditional Fiat--Shamir bound for the unified 33-round protocol, reusing
the existing v3 theorem. D1, D2, and D3 remain explicit obligations for the
caller-supplied extractor, decision, and round classifier. This theorem does
not instantiate them or assert a numerical security or privacy claim. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.UnifiedFiatShamir

open FS FS2 FS2.Duplex R0C.V3
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.OracleResampling
open AspisV8R19.CausalFirstHitUnionBound
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisR1.TranscriptView

variable {M Cv W : Type} {L : Nat}

theorem soundness_bound (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (decision : UnifiedSampler.Prefix M Cv L → Message M → Bool)
    (rb : RoundByRound' (UnifiedSampler.Public L) (Message M) (Challenge Cv)
      (Addr L) State)
    (pub : UnifiedSampler.Public L)
    (prover : Program (Addr L) State (UnifiedProtocol.Proof M))
    (hpub : pub.pubBytes.length < 2^32)
    (hl : ∀ n < 33, p.lbl n = UnifiedLabels.label n)
    (m0 : M) (he0 : p.enc m0 = PublicInitFrame.emptyRecord)
    (Qtot : Nat)
    (hD1 : FS2.D1 (UnifiedProtocol.protocol p hD extract) rb)
    (hD2 : FS2.D2 (UnifiedProtocol.protocol p hD extract) rb)
    (hD3 : FS2.D3 (UnifiedProtocol.protocol p hD extract) rb
      (fun x pf => UnifiedVerifier.verifier p hD extract decision x pf))
    (hQ : ∀ H, FS2.distinctFirstReads
      (eval H (FS2.experiment prover
        (fun x pf => UnifiedVerifier.verifier p hD extract decision x pf) pub)) ≤ Qtot) :
    mean (fun H : Addr L → State =>
      indicator
        (FS2.accepts (eval H (FS2.experiment prover
          (fun x pf => UnifiedVerifier.verifier p hD extract decision x pf) pub)) ∧
        FS2.extractFails (UnifiedProtocol.protocol p hD extract) pub
          (eval H (FS2.experiment prover
            (fun x pf => UnifiedVerifier.verifier p hD extract decision x pf) pub)))) ≤
      (Qtot : ℚ) * maxErr rb.ε 33 + 3 * (Qtot : ℚ)^2 / (256^32 : ℚ) := by
  exact R0C.V3.theorem43 (UnifiedProtocol.protocol p hD extract) rb
    (UnifiedDecoder.decode p hD pub) prover
    (fun x pf => UnifiedVerifier.verifier p hD extract decision x pf) pub
    UnifiedCollision.budget Qtot hD1
    (UnifiedChainDensity.chainDensity p hD extract rb hD2 pub) hD3
    (UnifiedProtocol.chainsRead p hD extract)
    (UnifiedFramework.readsChains p hD extract decision)
    (UnifiedInj.inj p hD extract decision pub prover hpub hl m0 he0 Qtot hQ) hQ

#print axioms soundness_bound

end AspisR1.UnifiedFiatShamir
end
