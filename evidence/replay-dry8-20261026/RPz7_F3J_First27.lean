import RPz7_F3J_RunState
import RPz7_F3J_PrefixWitness
import RPz7_F3J_SamplerCompose
import RPz7_F3J_CirclePair
import RPz7_F3J_SamplerStep
import RPz7_F3J_First25
import RPz7_F3J_InitialValue
import RPz7_F3J_SemanticPrefix
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3J_First27
open Aeneas Aeneas.Std Result FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisR1PublicPreparation SourceDigestAddresses SourceDigestLog SourceGlobalOracleInitial
open OraclePortCompactDraft PreparedHashCode

theorem sampler {Hash : Type} {D : aspis_core.Digest32 Hash} {pre : r1_wire.Prefix}
    {before after : r1_wire.SemanticTranscript Hash} {cs : List (SourceFull25.Call D pre)}
    (trace : SourceFull25.Trace D pre before after cs) (count : cs.length=25)
    {pubInput : pool_v1.pair_forest_semantic_terminal.r0.Public} {root : TranscriptStep.Bytes32}
    (init : PublicInitCall D pubInput root before)
    (B : FinishModel.Boundaries) (r25 r26 : r1_wire.ValidatedRecord)
    (t26 t27 : r1_wire.SemanticTranscript Hash) (z0 z1 : aspis_core.circle.SecureCirclePoint)
    (read25 : r1_wire.Prefix.validated_record pre 25#u8=ok (.Ok r25))
    (circle25 : FinishModel.circle_validated B D after r25=ok (.Ok z0,t26))
    (read26 : r1_wire.Prefix.validated_record pre 26#u8=ok (.Ok r26))
    (circle26 : FinishModel.circle_validated B D t26 r26=ok (.Ok z1,t27))
    (hash : Hash) (out : transcript.Transcript Hash)
    (reseed : transcript.Transcript.new D hash t27.state .S2=ok out)
    (H : Bytes → State) (backend : Tx1DigestLog.ByteOracleBackend D H)
    (p : Parsed) (rows : semanticRows 27 0 (slice p.wire 48 6983)=some p.semantic)
    (records : p.semantic=pre.records.val.map (fun s => MultiproofConeCanonical.bytesOf s.val))
    (w : CanonicalCutEnrichedTranscript.Words)
    (bound : ∀ row,(rowBytes p row).length≤SelectedTranscriptParams.D)
    (P : LiteralTranscript.Prefix) (tag : P.statement.tag=2)
    (publicBytes : P.statement.pubBytes=rawBytes (alloc.vec.Vec.deref init.encoded)) :
    let pf := F3J_InputRows.proof p (decodeState root) w bound
    (eval H (F3J_SamplerRun.program pf 0 27 P)).1=(initPair init::sourceLog cs)++
        (observe (run (S1SemanticCode.circleValidated B D after r25)).1 ++
        (observe (run (S1SemanticCode.circleValidated B D t26 r26)).1 ++
         observe (run (PreparedHashEffects.new effects D hash t27.state .S2)).1)) ∧
      UnifiedSampler.stateOf SelectedTranscriptParams.params
        (LiteralTranscript.erasePrefix (eval H (F3J_SamplerRun.program pf 0 27 P)).2)=decodeState out.state := by
  let pf := F3J_InputRows.proof p (decodeState root) w bound
  have firstRows := F3J_First25.sampler trace count init H backend p rows records w bound P publicBytes
  obtain ⟨middle,middleRun,middleState⟩ := F3J_PrefixWitness.pack H
    (F3J_SamplerRun.program pf 0 25 P) _
    (fun p => UnifiedSampler.stateOf SelectedTranscriptParams.params (LiteralTranscript.erasePrefix p)=decodeState after.state)
    firstRows.1 firstRows.2
  have middleTag : middle.statement.tag=2 :=
    (congrArg (fun p : LiteralTranscript.Public => p.tag)
      (F3J_PrefixWitness.carried_statement H pf 0 25 P middle _ middleRun)).trans tag
  have circles := F3J_CirclePair.sampler D B pre r25 r26 after t26 t27 z0 z1 read25 circle25
    read26 circle26 hash out reseed H backend p records (decodeState root) w bound middle middleTag middleState
  obtain ⟨last,lastRun,lastState⟩ := F3J_PrefixWitness.pack H
    (F3J_SamplerRun.program pf 25 2 middle) _
    (fun p => UnifiedSampler.stateOf SelectedTranscriptParams.params (LiteralTranscript.erasePrefix p)=decodeState out.state)
    circles.1 circles.2
  have combined := F3J_PrefixWitness.through H pf 0 25 2 P middle last _ _ middleRun lastRun
  constructor
  · exact congrArg Prod.fst combined
  · exact (F3J_RunState.of_run H _ _ last combined).trans lastState

#print axioms sampler
end AspisR1.F3J_First27
end
