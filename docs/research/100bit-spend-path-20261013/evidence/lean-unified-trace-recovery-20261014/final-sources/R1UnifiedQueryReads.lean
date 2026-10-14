import R1UnifiedQueryRun

/-! First-read membership for the actual row-31 query sampler in a unified
run, stated at its symbolic transcript prefix. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.UnifiedQueryReads

open FS FS2 FS2.Duplex R0C.V3
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open TranscriptView

variable {M Cv : Type} {L : Nat}

theorem row31_reads (p : Params M Cv L) (hD : 5 ≤ p.D)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (c1 : State) (payload : Nat → M) :
    let a := UnifiedQueryRun.queryAddress p hD H pub c1 payload
    a ∈ (eval H (UnifiedSampler.samp p hD 31
      (UnifiedRun.transcript p hD H pub c1 payload 31)
      (.payload (payload 31))).toProgram).1.map Prod.fst ∧
    ∀ j, j < 8 →
      squeezeA p (QuerySampler.state p H (H a) j) ∈
        (eval H (UnifiedSampler.samp p hD 31
          (UnifiedRun.transcript p hD H pub c1 payload 31)
          (.payload (payload 31))).toProgram).1.map Prod.fst ∧
      advanceA p (QuerySampler.state p H (H a) j) ∈
        (eval H (UnifiedSampler.samp p hD 31
          (UnifiedRun.transcript p hD H pub c1 payload 31)
          (.payload (payload 31))).toProgram).1.map Prod.fst := by
  dsimp
  rw [UnifiedSampler.row_query]
  constructor
  · exact QuerySamplerBridge.reads_absorb p H
      (UnifiedQueryRun.queryAddress p hD H pub c1 payload) UnifiedSampler.liftQuery
  · intro j hj
    exact QuerySamplerBridge.reads_pairs p H
      (UnifiedQueryRun.queryAddress p hD H pub c1 payload) UnifiedSampler.liftQuery j hj

#print axioms row31_reads

end AspisR1.UnifiedQueryReads
end
