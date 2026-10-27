import F3K_OpeningCalls
import F3K_SamplerOne
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3K_OpeningSuffix
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation PreparedHashCode
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortCompactDraft

theorem sampler {Hash : Type} {D : aspis_core.Digest32 Hash} {B : PreparedModel.Boundaries}
    {embed : aspis_core.field.M31 → Result aspis_core.field.WideExact}
    {v : verifier.View} {p : Parsed} (c : F3K_OpeningCalls.Calls D B embed v p)
    (H : Bytes → State) (backend : Tx1DigestLog.ByteOracleBackend D H)
    (root : State) (w : CanonicalCutEnrichedTranscript.Words)
    (bound : ∀ row,(rowBytes p row).length≤SelectedTranscriptParams.D)
    (P : LiteralTranscript.Prefix)
    (state : UnifiedSampler.stateOf SelectedTranscriptParams.params (LiteralTranscript.erasePrefix P)=decodeState c.t0.state) :
    let pf := F3J_InputRows.proof p root w bound
    (eval H (F3J_SamplerRun.program pf 27 6 P)).1=F3K_OpeningCalls.log c ∧
    UnifiedSampler.stateOf SelectedTranscriptParams.params
      (LiteralTranscript.erasePrefix (eval H (F3J_SamplerRun.program pf 27 6 P)).2)=decodeState c.t6.state := by
  let pf := F3J_InputRows.proof p root w bound
  let P27 := P
  let P28 := F3K_SamplerOne.next H pf 27 P27
  let P29 := F3K_SamplerOne.next H pf 28 P28
  let P30 := F3K_SamplerOne.next H pf 29 P29
  let P31 := F3K_SamplerOne.next H pf 30 P30
  let P32 := F3K_SamplerOne.next H pf 31 P31
  let P33 := F3K_SamplerOne.next H pf 32 P32
  have row27 := F3K_ScalarJoin.scalar D B c.t0 c.t1 27#u8 v.y1 c.gamma true
    c.firstCall H backend p root w bound (by decide) c.frame27
    (F3K_PayloadFits.fits v.y1 (rowBytes p 27) c.frame27 (bound 27)) P27 state
  have state28 : UnifiedSampler.stateOf SelectedTranscriptParams.params (LiteralTranscript.erasePrefix P28)=decodeState c.t1.state := by
    rw [F3K_SamplerOne.state]
    exact row27.2
  have row28 := F3K_ScalarJoin.scalar D B c.t1 c.t2 28#u8 (Array.to_slice c.inactive) c.kappa false
    c.secondCall H backend p root w bound (by decide) c.frame28
    (F3K_PayloadFits.fits (Array.to_slice c.inactive) (rowBytes p 28) c.frame28 (bound 28)) P28 state28
  have state29 : UnifiedSampler.stateOf SelectedTranscriptParams.params (LiteralTranscript.erasePrefix P29)=decodeState c.t2.state := by
    rw [F3K_SamplerOne.state]
    exact row28.2
  have row29 := F3K_ScalarJoin.scalar D B c.t2 c.t3 29#u8 v.round0 c.alpha0 false
    c.thirdCall H backend p root w bound (by decide) c.frame29
    (F3K_PayloadFits.fits v.round0 (rowBytes p 29) c.frame29 (bound 29)) P29 state29
  have state30 : UnifiedSampler.stateOf SelectedTranscriptParams.params (LiteralTranscript.erasePrefix P30)=decodeState c.t3.state := by
    rw [F3K_SamplerOne.state]
    exact row29.2
  have row30 := F3K_ScalarJoin.scalar D B c.t3 c.t4 30#u8 c.second.deref c.alpha1 false
    c.fourthCall H backend p root w bound (by decide) c.frame30
    (F3K_PayloadFits.fits c.second.deref (rowBytes p 30) c.frame30 (bound 30)) P30 state30
  have state31 : UnifiedSampler.stateOf SelectedTranscriptParams.params (LiteralTranscript.erasePrefix P31)=decodeState c.t4.state := by
    rw [F3K_SamplerOne.state]
    exact row30.2
  have row31 := F3K_QueryFull.exact_row D embed c.t4 c.t5 v.final_message c.queries c.queryCall
    H backend (F3K_PayloadFits.fits v.final_message (rowBytes p 31) c.frame31 (bound 31))
    P31 (pf 31) ⟨rowBytes p 31,bound 31⟩
    (by rw [F3J_InputRows.erased,if_neg (by decide)]) state31 c.frame31
  have state32 : UnifiedSampler.stateOf SelectedTranscriptParams.params (LiteralTranscript.erasePrefix P32)=decodeState c.t5.state := by
    rw [F3K_SamplerOne.state]
    exact congrArg (fun r=>r.2.2) row31
  have row32 := F3K_RhoJoin.rho D B c.t5 c.t6 PreparedScratchReachability.emptyPayload c.rho c.rhoCall
    H backend p root w bound c.frame32
    (F3K_PayloadFits.fits PreparedScratchReachability.emptyPayload (rowBytes p 32) c.frame32 (bound 32)) P32 state32
  have state33 : UnifiedSampler.stateOf SelectedTranscriptParams.params (LiteralTranscript.erasePrefix P33)=decodeState c.t6.state := by
    rw [F3K_SamplerOne.state]
    exact row32.2
  have logs31 := congrArg Prod.fst row31
  constructor
  · change (eval H (F3J_SamplerRun.program pf 27 6 P)).1=_
    simp only [F3J_SamplerRun.program,eval_bind,eval,List.append_nil]
    change (eval H (LiteralByteSampler.samp 27 P27 (pf 27)).toProgram).1 ++
      (eval H (LiteralByteSampler.samp 28 P28 (pf 28)).toProgram).1 ++
      (eval H (LiteralByteSampler.samp 29 P29 (pf 29)).toProgram).1 ++
      (eval H (LiteralByteSampler.samp 30 P30 (pf 30)).toProgram).1 ++
      (eval H (LiteralByteSampler.samp 31 P31 (pf 31)).toProgram).1 ++
      (eval H (LiteralByteSampler.samp 32 P32 (pf 32)).toProgram).1=_
    erw [row27.1,row28.1,row29.1,row30.1,logs31,row32.1]
    rfl
  · change UnifiedSampler.stateOf SelectedTranscriptParams.params
      (LiteralTranscript.erasePrefix (eval H (F3J_SamplerRun.program pf 27 6 P)).2)=_
    have endPrefix : (eval H (F3J_SamplerRun.program pf 27 6 P)).2=P33 := by
      simp only [F3J_SamplerRun.program,eval_bind,eval]
      rfl
    rw [endPrefix]
    exact state33

#print axioms sampler
end AspisR1.F3K_OpeningSuffix
end
