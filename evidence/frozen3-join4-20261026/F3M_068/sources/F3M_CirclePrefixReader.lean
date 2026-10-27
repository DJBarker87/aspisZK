import F3M_CircleEntries
import F3M_CircleReader
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3M_CirclePrefixReader
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw OraclePortCompactDraft
attribute [local irreducible] F3J_InputRows.proof F3J_SamplerRun.program

theorem parameters {Hash : Type} (D : aspis_core.Digest32 Hash) (B : FinishModel.Boundaries)
    (pre : r1_wire.Prefix) (r25 r26 : r1_wire.ValidatedRecord)
    (t25 t26 t27 : r1_wire.SemanticTranscript Hash) (z0 z1 : aspis_core.circle.SecureCirclePoint)
    (read25 : r1_wire.Prefix.validated_record pre 25#u8=ok (.Ok r25))
    (circle25 : FinishModel.circle_validated B D t25 r25=ok (.Ok z0,t26))
    (read26 : r1_wire.Prefix.validated_record pre 26#u8=ok (.Ok r26))
    (circle26 : FinishModel.circle_validated B D t26 r26=ok (.Ok z1,t27))
    (hash : Hash) (out : transcript.Transcript Hash)
    (reseed : transcript.Transcript.new D hash t27.state .S2=ok out)
    (H : Bytes → State) (backend : Tx1DigestLog.ByteOracleBackend D H)
    (p : Parsed) (records : p.semantic=pre.records.val.map (fun s=>MultiproofConeCanonical.bytesOf s.val))
    (root : State) (w : CanonicalCutEnrichedTranscript.Words)
    (bound : ∀ row,(rowBytes p row).length≤SelectedTranscriptParams.D)
    (P : LiteralTranscript.Prefix) (length : P.rounds.length=25) (tag : P.statement.tag=2)
    (state : UnifiedSampler.stateOf SelectedTranscriptParams.params (LiteralTranscript.erasePrefix P)=decodeState t25.state)
    (tail : Nat) (q : Fin 22 → Fin 262144) (v : LiteralOpeningView.View)
    (opening : LiteralOpeningView.read (OraclePortStoredDecisionDraftC4.typedRows p q
      (LiteralTranscript.erasePrefix (eval H (F3J_SamplerRun.program
        (F3J_InputRows.proof p root w bound) 25 (tail+2) P)).2))=some v) :
    ∃ b0 b1,B.circle b0 .First=ok z0 ∧ B.circle b1 .Second=ok z1 ∧
      v.challenge25=SelectedTranscriptParams.params.σ 25 (decodeState b0) ∧
      v.challenge26=SelectedTranscriptParams.params.σ 26 (decodeState b1) := by
  let pf := F3J_InputRows.proof p root w bound
  let P26 := P.ext (pf 25) (eval H (LiteralByteSampler.samp 25 P (pf 25)).toProgram).2
  have source := F3J_CircleJoin.first D B pre r25 t25 t26 z0 read25 circle25 H backend p records
    root w bound P state
  have state26 : UnifiedSampler.stateOf SelectedTranscriptParams.params (LiteralTranscript.erasePrefix P26)=decodeState t26.state := by
    dsimp only [P26]
    rw [LiteralTranscript.erasePrefix_ext,UnifiedSampler.stateOf_ext]
    exact source.2
  have length26 : P26.rounds.length=26 := by
    simp only [P26,FS.Prefix.ext,List.length_append,List.length_singleton,length]
  obtain ⟨b0,c0,e0⟩ := F3M_CircleEntries.first D B pre r25 t25 t26 z0 read25 circle25
    H backend p records root w bound P state length (tail+1)
  obtain ⟨b1,c1,e1⟩ := F3M_CircleEntries.second D B pre r26 t26 t27 z1 read26 circle26
    hash out reseed H backend p records root w bound P26 tag state26 length26 tail
  have split := congrArg Prod.snd (F3J_SamplerStep.step H pf 25 (tail+1) P)
  have secondEntry := (congrArg (fun Q : LiteralTranscript.Prefix=>Q.rounds[26]?) split).trans e1
  exact ⟨b0,b1,c0,c1,F3M_CircleReader.first p q _ v _ _ _ e0 opening,
    F3M_CircleReader.second p q _ v _ _ _ secondEntry opening⟩

#print axioms parameters
end AspisR1.F3M_CirclePrefixReader
end
