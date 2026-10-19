import R1UnifiedSampler

/-! Deterministic transcript continuation facts for the unified sampler. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.UnifiedContinuation

open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open TranscriptView
open AspisR1.UnifiedSampler

variable {M Cv : Type} {L : Nat}

theorem absorb_ext (p : Params M Cv L) (i : Nat) (P : Prefix M Cv L)
    (m : Message M) (ch : Challenge Cv) (next : M) :
    absorb p i (P.ext m ch) next =
      absorbA p ch.2 (p.lbl i) (p.enc next) (p.encLen next) := by
  simp [UnifiedSampler.absorb, stateOf_ext]

theorem query_then_rho_state (p : Params M Cv L) (hD : 5 ≤ p.D)
    (P : Prefix M Cv L) (qm : M) (H : Addr L → State) :
    let a := absorb p 31 P qm
    let qr := QueryFirstRead.result p H (QuerySampler.state p H (H a))
    stateOf p (P.ext (.payload qm)
      (eval H (samp p hD 31 P (.payload qm)).toProgram).2) = qr.2 := by
  intro a qr
  rw [stateOf_ext, row_query, QuerySamplerBridge.output]
  rfl

theorem query_then_rho_firstCell (p : Params M Cv L) (hD : 5 ≤ p.D)
    (P : Prefix M Cv L) (qm rm : M) (H : Addr L → State) :
    let a := absorb p 31 P qm
    let qr := QueryFirstRead.result p H (QuerySampler.state p H (H a))
    firstCell (samp p hD 32
      (P.ext (.payload qm) (eval H (samp p hD 31 P (.payload qm)).toProgram).2)
      (.payload rm)) =
      some (absorbA p qr.2 (p.lbl 32) (p.enc rm) (p.encLen rm)) := by
  intro a qr
  rw [row_rho]
  change some (absorb p 32
    (P.ext (.payload qm) (eval H (samp p hD 31 P (.payload qm)).toProgram).2) rm) = _
  rw [absorb_ext, row_query, QuerySamplerBridge.output]
  rfl

#print axioms absorb_ext
#print axioms query_then_rho_state
#print axioms query_then_rho_firstCell

end AspisR1.UnifiedContinuation
end
