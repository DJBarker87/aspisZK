import F3K_OpeningPair27
import F3K_OpeningPair29
import F3K_SamplerOne
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3K_OpeningFirst4
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
    (eval H (F3J_SamplerRun.program pf 27 4 P)).1=
      observe (run (PreparedScalarEffects.scalar effects B D c.t0 27#u8 v.y1 true)).1 ++
      observe (run (PreparedScalarEffects.scalar effects B D c.t1 28#u8 (Array.to_slice c.inactive) false)).1 ++
      observe (run (PreparedScalarEffects.scalar effects B D c.t2 29#u8 v.round0 false)).1 ++
      observe (run (PreparedScalarEffects.scalar effects B D c.t3 30#u8 c.second.deref false)).1 ∧
    UnifiedSampler.stateOf SelectedTranscriptParams.params
      (LiteralTranscript.erasePrefix (eval H (F3J_SamplerRun.program pf 27 4 P)).2)=decodeState c.t4.state := by
  let pf := F3J_InputRows.proof p root w bound
  have first := F3K_OpeningPair27.sampler c H backend root w bound P state
  let P29 := (eval H (F3J_SamplerRun.program pf 27 2 P)).2
  have second := F3K_OpeningPair29.sampler c H backend root w bound P29 first.2
  constructor
  · have logs := (F3J_SamplerCompose.logs H pf 27 2 2 P).trans
      (congrArg₂ List.append first.1 second.1)
    simpa only [List.append_assoc] using (logs.trans (List.append_assoc _ _ _))
  · exact (congrArg (fun Q=>UnifiedSampler.stateOf SelectedTranscriptParams.params
      (LiteralTranscript.erasePrefix Q)) (F3J_SamplerCompose.value H pf 27 2 2 P)).trans second.2

#print axioms sampler
end AspisR1.F3K_OpeningFirst4
end
