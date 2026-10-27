import RPz7_F3K_OpeningCalls
import RPz7_F3K_ScalarOne
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3K_OpeningPair29
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation PreparedHashCode
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw
open OraclePortCompactDraft

theorem sampler {Hash : Type} {D : aspis_core.Digest32 Hash} {B : PreparedModel.Boundaries}
    {embed : aspis_core.field.M31 → Result aspis_core.field.WideExact}
    {v : verifier.View} {p : Parsed} (c : F3K_OpeningCalls.Calls D B embed v p)
    (H : Bytes → State) (backend : Tx1DigestLog.ByteOracleBackend D H)
    (root : State) (w : CanonicalCutEnrichedTranscript.Words)
    (bound : ∀ row,(rowBytes p row).length≤SelectedTranscriptParams.D)
    (P : LiteralTranscript.Prefix)
    (state : UnifiedSampler.stateOf SelectedTranscriptParams.params (LiteralTranscript.erasePrefix P)=decodeState c.t2.state) :
    let pf := F3J_InputRows.proof p root w bound
    (eval H (F3J_SamplerRun.program pf 29 2 P)).1=
      observe (run (PreparedScalarEffects.scalar effects B D c.t2 29#u8 v.round0 false)).1 ++
      observe (run (PreparedScalarEffects.scalar effects B D c.t3 30#u8 c.second.deref false)).1 ∧
    UnifiedSampler.stateOf SelectedTranscriptParams.params
      (LiteralTranscript.erasePrefix (eval H (F3J_SamplerRun.program pf 29 2 P)).2)=decodeState c.t4.state := by
  let pf := F3J_InputRows.proof p root w bound
  let P30 := (eval H (F3J_SamplerRun.program pf 29 1 P)).2
  have h29 := F3K_ScalarOne.scalar D B c.t2 c.t3 29#u8 v.round0 c.alpha0 false c.thirdCall H backend
    p root w bound (by decide) c.frame29
    (F3K_PayloadFits.fits v.round0 (rowBytes p 29) c.frame29 (bound 29)) P state
  have h30 := F3K_ScalarOne.scalar D B c.t3 c.t4 30#u8 c.second.deref c.alpha1 false c.fourthCall H backend
    p root w bound (by decide) c.frame30
    (F3K_PayloadFits.fits c.second.deref (rowBytes p 30) c.frame30 (bound 30)) P30 h29.2
  constructor
  · exact (F3J_SamplerCompose.logs H pf 29 1 1 P).trans (congrArg₂ List.append h29.1 h30.1)
  · exact (congrArg (fun Q=>UnifiedSampler.stateOf SelectedTranscriptParams.params
      (LiteralTranscript.erasePrefix Q)) (F3J_SamplerCompose.value H pf 29 1 1 P)).trans h30.2

#print axioms sampler
end AspisR1.F3K_OpeningPair29
end
