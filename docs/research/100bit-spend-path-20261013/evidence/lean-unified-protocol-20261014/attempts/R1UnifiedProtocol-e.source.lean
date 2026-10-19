import R1UnifiedRun
import FS2.Verifier

/-! A concrete FS2 protocol record for the unified 33-row sampler schedule.
The decoder field is totalized to `none`; the FS2 V3 framework does not use
that field in the transcript, chain, or `ChainsRead` statements proved here.
The extractor remains an explicit argument. This module makes no acceptance,
decoder, or soundness claim. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.UnifiedProtocol

open FS FS2
open FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisR1.TranscriptView

variable {M Cv : Type} {L : Nat}

abbrev Proof (M : Type) := State × (Nat → M)

def protocol {W : Type} (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W) :
    FS2.Protocol (UnifiedSampler.Public L) (Message M) (Challenge Cv) W
      (Proof M) (Addr L) State where
  r := 33
  msg := fun π => UnifiedRun.message π.1 π.2
  samp := UnifiedSampler.samp p hD
  decode := fun _ _ => none
  extract := extract

theorem transcript_eq {W : Type} (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (H : Addr L → State) (pub : UnifiedSampler.Public L) (π : Proof M) :
    ∀ n, (protocol p hD extract).transcript H pub π n =
      UnifiedRun.transcript p hD H pub π.1 π.2 n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [FS2.Protocol.transcript, protocol, UnifiedRun.transcript, ih]

theorem chain_eq {W : Type} (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (H : Addr L → State) (pub : UnifiedSampler.Public L) (π : Proof M)
    (i : Nat) :
    (protocol p hD extract).chain H pub π i =
      UnifiedSampler.samp p hD i (UnifiedRun.transcript p hD H pub π.1 π.2 i)
        (UnifiedRun.message π.1 π.2 i) := by
  simp [FS2.Protocol.chain, protocol, transcript_eq]

theorem chal_eq {W : Type} (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (H : Addr L → State) (pub : UnifiedSampler.Public L) (π : Proof M)
    (i : Nat) :
    (protocol p hD extract).chal H pub π i =
      (eval H (UnifiedSampler.samp p hD i
        (UnifiedRun.transcript p hD H pub π.1 π.2 i)
        (UnifiedRun.message π.1 π.2 i)).toProgram).2 := by
  change (eval H ((protocol p hD extract).chain H pub π i).toProgram).2 = _
  rw [chain_eq]

theorem chainsRead {W : Type} (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W) :
    FS2.ChainsRead (protocol p hD extract) := by
  intro i P m hi
  exact UnifiedSampler.firstCell_some p hD i P m

#print axioms transcript_eq
#print axioms chain_eq
#print axioms chal_eq
#print axioms chainsRead

end AspisR1.UnifiedProtocol
end
