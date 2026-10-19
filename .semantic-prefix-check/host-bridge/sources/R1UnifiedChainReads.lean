import R1UnifiedSteps

/-! Hash reads of the actual unified run, including both special hash edges.
These are deterministic read-set facts; no decoder or security conclusion
is assumed. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.UnifiedChainReads

open FS FS2 FS2.Duplex
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open TranscriptView

variable {M Cv : Type} {L : Nat}
variable (p : Params M Cv L) (hD : 5 ≤ p.D) (H : Addr L → State)
  (pub : UnifiedSampler.Public L) (c1 : State) (payload : Nat → M)

def chain (i : Nat) : Sampler (Addr L) State (Challenge Cv) :=
  UnifiedSampler.samp p hD i (UnifiedRun.transcript p hD H pub c1 payload i)
    (UnifiedRun.message c1 payload i)

theorem initial_read :
    PublicInitFrame.addr pub.pubBytes pub.initFits c1 ∈
      (eval H (chain p hD H pub c1 payload 0).toProgram).1.map Prod.fst := by
  change PublicInitFrame.addr pub.pubBytes pub.initFits c1 ∈
    (eval H (DuplexSamplers.initial p
      (PublicInitFrame.addr pub.pubBytes pub.initFits c1)
      (PublicInitFrame.row0 p hD) 0 liftChallenge).toProgram).1.map Prod.fst
  rw [DuplexSamplers.initial_eval]
  simp

theorem ordinary_reads (hl : p.lbl 0 = 160)
    (he : p.enc (payload 0) = PublicInitFrame.emptyRecord)
    (i : Nat) (hi31 : i ≠ 31) :
    UnifiedSteps.address p hD H pub c1 payload i ∈
      (eval H (chain p hD H pub c1 payload i).toProgram).1.map Prod.fst ∧
    squeezeA p (UnifiedRecords.absorbed p hD H pub c1 payload i) ∈
      (eval H (chain p hD H pub c1 payload i).toProgram).1.map Prod.fst ∧
    advanceA p (UnifiedRecords.absorbed p hD H pub c1 payload i) ∈
      (eval H (chain p hD H pub c1 payload i).toProgram).1.map Prod.fst := by
  cases i with
  | zero =>
      change _ ∈ (eval H (DuplexSamplers.initial p
        (PublicInitFrame.addr pub.pubBytes pub.initFits c1)
        (PublicInitFrame.row0 p hD) 0 liftChallenge).toProgram).1.map Prod.fst ∧
        _ ∈ (eval H (DuplexSamplers.initial p
        (PublicInitFrame.addr pub.pubBytes pub.initFits c1)
        (PublicInitFrame.row0 p hD) 0 liftChallenge).toProgram).1.map Prod.fst ∧
        _ ∈ (eval H (DuplexSamplers.initial p
        (PublicInitFrame.addr pub.pubBytes pub.initFits c1)
        (PublicInitFrame.row0 p hD) 0 liftChallenge).toProgram).1.map Prod.fst
      rw [DuplexSamplers.initial_eval,
        UnifiedSteps.initial_address p hD H pub c1 payload hl he]
      have ha : H (UnifiedSteps.address p hD H pub c1 payload 0) =
          UnifiedRecords.absorbed p hD H pub c1 payload 0 := rfl
      rw [ha]
      simp
  | succ i =>
      have hr := UnifiedPayloadStep.payload_reads p hD H (i + 1) (by omega)
        hi31 (UnifiedRun.transcript p hD H pub c1 payload (i + 1))
        (payload (i + 1))
      dsimp only at hr
      rw [UnifiedSteps.payload_address p hD H pub c1 payload (i + 1) (by omega)] at hr
      exact hr

theorem reseed_read :
    UnifiedSteps.reseedAddress p hD H pub c1 payload ∈
      (eval H (chain p hD H pub c1 payload 26).toProgram).1.map Prod.fst := by
  have hr := UnifiedPayloadStep.reseed_read p hD H
    (UnifiedRun.transcript p hD H pub c1 payload 26) (payload 26)
  rw [UnifiedSteps.payload_absorbed p hD H pub c1 payload 26 (by decide)] at hr
  simp only [UnifiedRun.transcript_statement] at hr
  exact hr

#print axioms initial_read
#print axioms ordinary_reads
#print axioms reseed_read

end AspisR1.UnifiedChainReads
end
