import R1UnifiedFramework
import R1UnifiedExperimentInjection

/-! The experiment's row-32 first cell identifies the rho endpoint, so the
existing rho-only decoder/follow result can be stated directly at the actual
FS2 protocol chain. This remains a case bridge, not a global Inj3 theorem. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.UnifiedRhoCase

open FS FS2 FS2.Duplex R0C.V3
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open TranscriptView

variable {M Cv W : Type} {L : Nat}

theorem decodes_and_follows (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (decision : UnifiedSampler.Prefix M Cv L → Message M → Bool)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (prover : Program (Addr L) State (UnifiedProtocol.Proof M))
    (hpub : pub.pubBytes.length < 2^32)
    (hl : p.lbl 0 = 160)
    (he : p.enc ((eval H prover).2.2 0) = PublicInitFrame.emptyRecord)
    (Qtot : Nat)
    (hQ : firstReads emptyTable
      (eval H (FS.experiment prover
        (fun x pf => UnifiedVerifier.verifier p hD extract decision x pf) pub)).1 ≤ Qtot)
    (hold : ¬ hitsBad (badColl p Qtot) emptyTable
      (eval H (FS.experiment prover
        (fun x pf => UnifiedVerifier.verifier p hD extract decision x pf) pub)).1)
    (htail : ¬ hitsBad (ParsedStateCollision.bad TrailingStateFrame.tailState Qtot)
      emptyTable (eval H (FS.experiment prover
        (fun x pf => UnifiedVerifier.verifier p hD extract decision x pf) pub)).1)
    (a : Addr L)
    (hfirst : firstCell ((UnifiedProtocol.protocol p hD extract).chain H pub
      (eval H prover).2 32) = some a) :
    let π := (eval H prover).2
    let tr := (eval H (FS.experiment prover
      (fun x pf => UnifiedVerifier.verifier p hD extract decision x pf) pub)).1
    let T := tableBefore emptyTable tr a
    ∃ own pend g,
      JointUnifiedDecoder.decode p pub 27 4 a T = some (own, pend, g) ∧
      bfollow g (traceFrom tr a) own pend T =
        some ((UnifiedProtocol.protocol p hD extract).transcript H pub π 32,
          (UnifiedProtocol.protocol p hD extract).msg π 32,
          (UnifiedProtocol.protocol p hD extract).chal H pub π 32) := by
  let π := (eval H prover).2
  let tr := (eval H (FS.experiment prover
    (fun x pf => UnifiedVerifier.verifier p hD extract decision x pf) pub)).1
  let c := UnifiedQueryRun.rhoAddress p hD H pub π.1 π.2
  have hrho := UnifiedFramework.rho_firstCell p hD extract H pub π.1 π.2
  have hac : a = c := Option.some.inj (hfirst.symm.trans hrho)
  subst a
  have hresult := UnifiedExperimentInjection.decodes_and_follows p hD extract
    decision H pub prover hpub hl he Qtot hQ hold htail
  simpa only [c, π, UnifiedProtocol.transcript_eq, UnifiedProtocol.chal_eq] using hresult

#print axioms decodes_and_follows

end AspisR1.UnifiedRhoCase
end
