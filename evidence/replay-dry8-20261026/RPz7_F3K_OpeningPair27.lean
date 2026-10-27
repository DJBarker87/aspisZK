import RPz7_F3K_OpeningCalls
import RPz7_F3K_ScalarOne
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3K_OpeningPair27
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
    (state : UnifiedSampler.stateOf SelectedTranscriptParams.params (LiteralTranscript.erasePrefix P)=decodeState c.t0.state) :
    let pf := F3J_InputRows.proof p root w bound
    (eval H (F3J_SamplerRun.program pf 27 2 P)).1=
      observe (run (PreparedScalarEffects.scalar effects B D c.t0 27#u8 v.y1 true)).1 ++
      observe (run (PreparedScalarEffects.scalar effects B D c.t1 28#u8 (Array.to_slice c.inactive) false)).1 ∧
    UnifiedSampler.stateOf SelectedTranscriptParams.params
      (LiteralTranscript.erasePrefix (eval H (F3J_SamplerRun.program pf 27 2 P)).2)=decodeState c.t2.state := by
  let pf := F3J_InputRows.proof p root w bound
  let P28 := (eval H (F3J_SamplerRun.program pf 27 1 P)).2
  have h27 := F3K_ScalarOne.scalar D B c.t0 c.t1 27#u8 v.y1 c.gamma true c.firstCall H backend
    p root w bound (by decide) c.frame27
    (F3K_PayloadFits.fits v.y1 (rowBytes p 27) c.frame27 (bound 27)) P state
  have h28 := F3K_ScalarOne.scalar D B c.t1 c.t2 28#u8 (Array.to_slice c.inactive) c.kappa false c.secondCall H backend
    p root w bound (by decide) c.frame28
    (F3K_PayloadFits.fits (Array.to_slice c.inactive) (rowBytes p 28) c.frame28 (bound 28)) P28 h27.2
  constructor
  · exact (F3J_SamplerCompose.logs H pf 27 1 1 P).trans (congrArg₂ List.append h27.1 h28.1)
  · exact (congrArg (fun Q=>UnifiedSampler.stateOf SelectedTranscriptParams.params
      (LiteralTranscript.erasePrefix Q)) (F3J_SamplerCompose.value H pf 27 1 1 P)).trans h28.2

#print axioms sampler
end AspisR1.F3K_OpeningPair27
end
