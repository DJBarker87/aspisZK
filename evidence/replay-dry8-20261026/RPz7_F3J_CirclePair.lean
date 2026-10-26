import RPz7_F3J_CircleJoin
import RPz7_F3J_SamplerStructure
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3J_CirclePair
open Aeneas Aeneas.Std Result FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw
open AspisR1PublicPreparation PreparedHashCode OraclePortCompactDraft

theorem sampler {Hash : Type} (D : aspis_core.Digest32 Hash) (B : FinishModel.Boundaries)
    (pre : r1_wire.Prefix) (r25 r26 : r1_wire.ValidatedRecord)
    (t25 t26 t27 : r1_wire.SemanticTranscript Hash) (z0 z1 : aspis_core.circle.SecureCirclePoint)
    (read25 : r1_wire.Prefix.validated_record pre 25#u8=ok (.Ok r25))
    (circle25 : FinishModel.circle_validated B D t25 r25=ok (.Ok z0,t26))
    (read26 : r1_wire.Prefix.validated_record pre 26#u8=ok (.Ok r26))
    (circle26 : FinishModel.circle_validated B D t26 r26=ok (.Ok z1,t27))
    (hash : Hash) (out : transcript.Transcript Hash)
    (reseed : transcript.Transcript.new D hash t27.state .S2=ok out)
    (H : Bytes → State) (backend : Tx1DigestLog.ByteOracleBackend D H)
    (p : Parsed) (records : p.semantic=pre.records.val.map (fun s => MultiproofConeCanonical.bytesOf s.val))
    (root : State) (w : CanonicalCutEnrichedTranscript.Words)
    (bound : ∀ row,(rowBytes p row).length≤SelectedTranscriptParams.D)
    (P : LiteralTranscript.Prefix) (tag : P.statement.tag=2)
    (state : UnifiedSampler.stateOf SelectedTranscriptParams.params (LiteralTranscript.erasePrefix P)=decodeState t25.state) :
    let pf := F3J_InputRows.proof p root w bound
    (eval H (F3J_SamplerRun.program pf 25 2 P)).1=
      observe (run (S1SemanticCode.circleValidated B D t25 r25)).1 ++
      (observe (run (S1SemanticCode.circleValidated B D t26 r26)).1 ++
       observe (run (PreparedHashEffects.new effects D hash t27.state .S2)).1) ∧
    UnifiedSampler.stateOf SelectedTranscriptParams.params
      (LiteralTranscript.erasePrefix (eval H (F3J_SamplerRun.program pf 25 2 P)).2)=decodeState out.state := by
  let pf := F3J_InputRows.proof p root w bound
  have first := F3J_CircleJoin.first D B pre r25 t25 t26 z0 read25 circle25 H backend p records root w bound P state
  let middle := P.ext (pf 25) (eval H (LiteralByteSampler.samp 25 P (pf 25)).toProgram).2
  have nextState : UnifiedSampler.stateOf SelectedTranscriptParams.params
      (LiteralTranscript.erasePrefix middle)=decodeState t26.state := by
    dsimp only [middle]
    rw [LiteralTranscript.erasePrefix_ext,UnifiedSampler.stateOf_ext]
    exact first.2
  have nextTag : middle.statement.tag=2 := tag
  have second := F3J_CircleJoin.second D B pre r26 t26 t27 z1 read26 circle26 hash out reseed
    H backend p records root w bound middle nextTag nextState
  have expanded := F3J_SamplerStructure.pair H pf 25 P
  change eval H (F3J_SamplerRun.program (F3J_InputRows.proof p root w bound) 25 2 P)=_ at expanded
  dsimp only
  rw [expanded]
  constructor
  · exact congrArg₂ List.append first.1 second.1
  · change UnifiedSampler.stateOf SelectedTranscriptParams.params
      (LiteralTranscript.erasePrefix (middle.ext (pf 26)
        (eval H (LiteralByteSampler.samp 26 middle (pf 26)).toProgram).2))=_
    rw [LiteralTranscript.erasePrefix_ext,UnifiedSampler.stateOf_ext]
    exact second.2

#print axioms sampler
end AspisR1.F3J_CirclePair
end
