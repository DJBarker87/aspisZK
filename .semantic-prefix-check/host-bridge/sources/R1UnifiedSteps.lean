import R1UnifiedRecords
import R1UnifiedPayloadStep

/-! Hash-chain transitions derived from the unified deterministic run.
Row zero and row 26 retain their explicit extra hash edges. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.UnifiedSteps

open FS FS2 FS2.Duplex
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open TranscriptView

variable {M Cv : Type} {L : Nat}
variable (p : Params M Cv L) (hD : 5 ≤ p.D) (H : Addr L → State)
  (pub : UnifiedSampler.Public L) (c1 : State) (payload : Nat → M)

def address (i : Nat) : Addr L :=
  absorbA p (UnifiedRecords.previous p hD H pub c1 payload i)
    (p.lbl i) (p.enc (payload i)) (p.encLen (payload i))

theorem payload_address (i : Nat) (hi : i ≠ 0) :
    UnifiedSampler.absorb p i (UnifiedRun.transcript p hD H pub c1 payload i)
      (payload i) = address p hD H pub c1 payload i := by
  cases i with
  | zero => contradiction
  | succ i => rfl

theorem payload_absorbed (i : Nat) (hi : i ≠ 0) :
    H (UnifiedSampler.absorb p i (UnifiedRun.transcript p hD H pub c1 payload i)
      (payload i)) = UnifiedRecords.absorbed p hD H pub c1 payload i := by
  rw [payload_address p hD H pub c1 payload i hi]
  rfl

theorem initial_address (hl : p.lbl 0 = 160)
    (he : p.enc (payload 0) = PublicInitFrame.emptyRecord) :
    PublicInitFrame.row0 p hD (H (PublicInitFrame.addr pub.pubBytes pub.initFits c1)) =
      address p hD H pub c1 payload 0 :=
  RowZeroCodec.row0_absorb p hD (payload 0) hl he _

def reseedAddress : Addr L :=
  OpeningReseedFrame.addr pub.tag (by have := pub.initFits; omega)
    (H (advanceA p (UnifiedRecords.absorbed p hD H pub c1 payload 26)))

theorem state_step (hl : p.lbl 0 = 160)
    (he : p.enc (payload 0) = PublicInitFrame.emptyRecord)
    (i : Nat) (h26 : i ≠ 26) (h31 : i ≠ 31) :
    UnifiedRun.state p hD H pub c1 payload (i + 1) =
      H (advanceA p (UnifiedRecords.absorbed p hD H pub c1 payload i)) := by
  rw [UnifiedRun.state_succ]
  cases i with
  | zero =>
      change (eval H (DuplexSamplers.initial p
        (PublicInitFrame.addr pub.pubBytes pub.initFits c1)
        (PublicInitFrame.row0 p hD) 0 liftChallenge).toProgram).2.2 = _
      rw [DuplexSamplers.initial_eval]
      dsimp only [liftChallenge]
      rw [initial_address p hD H pub c1 payload hl he]
      rfl
  | succ i =>
      change (eval H (UnifiedSampler.samp p hD (i + 1)
        (UnifiedRun.transcript p hD H pub c1 payload (i + 1))
        (.payload (payload (i + 1)))).toProgram).2.2 = _
      rw [UnifiedPayloadStep.payload_step p hD H (i + 1) (by omega) h26 h31,
        payload_absorbed p hD H pub c1 payload (i + 1) (by omega)]

theorem reseed_step :
    UnifiedRun.state p hD H pub c1 payload 27 =
      H (reseedAddress p hD H pub c1 payload) := by
  rw [UnifiedRun.state_succ]
  change (eval H (UnifiedSampler.samp p hD 26
    (UnifiedRun.transcript p hD H pub c1 payload 26)
    (.payload (payload 26))).toProgram).2.2 = _
  rw [UnifiedPayloadStep.reseed_step,
    payload_absorbed p hD H pub c1 payload 26 (by decide)]
  simp only [UnifiedRun.transcript_statement]
  rfl

#print axioms payload_address
#print axioms payload_absorbed
#print axioms initial_address
#print axioms state_step
#print axioms reseed_step

end AspisR1.UnifiedSteps
end
