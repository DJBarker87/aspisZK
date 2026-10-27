import RPz7_F3J_SamplerStep
import RPz7_F3J_InitialValue
import RPz7_F3J_SemanticPrefix
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3J_First25
open Aeneas Aeneas.Std Result FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisR1PublicPreparation SourceDigestAddresses SourceDigestLog SourceGlobalOracleInitial
open OraclePortCompactDraft

theorem sampler {Hash : Type} {D : aspis_core.Digest32 Hash} {pre : r1_wire.Prefix}
    {before after : r1_wire.SemanticTranscript Hash} {cs : List (SourceFull25.Call D pre)}
    (trace : SourceFull25.Trace D pre before after cs) (count : cs.length=25)
    {pubInput : pool_v1.pair_forest_semantic_terminal.r0.Public} {root : TranscriptStep.Bytes32}
    (init : PublicInitCall D pubInput root before)
    (H : Bytes → State) (backend : Tx1DigestLog.ByteOracleBackend D H)
    (p : Parsed) (rows : semanticRows 27 0 (slice p.wire 48 6983)=some p.semantic)
    (records : p.semantic=pre.records.val.map (fun s => MultiproofConeCanonical.bytesOf s.val))
    (w : CanonicalCutEnrichedTranscript.Words)
    (bound : ∀ row,(rowBytes p row).length≤SelectedTranscriptParams.D)
    (P : LiteralTranscript.Prefix)
    (publicBytes : P.statement.pubBytes=rawBytes (alloc.vec.Vec.deref init.encoded)) :
    let pf := F3J_InputRows.proof p (decodeState root) w bound
    (eval H (F3J_SamplerRun.program pf 0 25 P)).1=initPair init::sourceLog cs ∧
      UnifiedSampler.stateOf SelectedTranscriptParams.params
        (LiteralTranscript.erasePrefix (eval H (F3J_SamplerRun.program pf 0 25 P)).2)=decodeState after.state := by
  dsimp only
  cases trace with
  | nil self => cases count
  | @cons after cs c tail =>
    have rowC : c.row.val=0 := by
      rw [← c.record_row,c.before_row,init.carried]
      rfl
    have nextC : c.after.next_row.val=1 := by
      rw [c.carried]
      change c.next.val=1
      rw [c.next_row,c.record_row,rowC]
    have len : cs.length=24 := by simp only [List.length_cons] at count; omega
    let pf := F3J_InputRows.proof p (decodeState root) w bound
    have initial : eval H (LiteralByteSampler.samp 0 P (pf 0)).toProgram=
        (initPair init::callLog c,(TranscriptView.Value.ordinary (SourceLiteralTraceLift.sourceChallenge c),decodeState c.after.state)) :=
      F3J_InitialValue.initial c init rowC (F3J_RowBindings.first c p rows records rowC)
        H backend P w.c1 publicBytes
    let next := P.ext (pf 0) (.ordinary (SourceLiteralTraceLift.sourceChallenge c),decodeState c.after.state)
    have nextState : UnifiedSampler.stateOf SelectedTranscriptParams.params
        (LiteralTranscript.erasePrefix next)=decodeState c.after.state := by
      dsimp only [next]
      rw [LiteralTranscript.erasePrefix_ext,UnifiedSampler.stateOf_ext]
    have result := F3J_SemanticPrefix.positive tail H backend p records (decodeState root) w bound
      1 next (by decide) (by omega) nextC nextState
    have expanded := F3J_SamplerStep.step H pf 0 24 P
    rw [initial] at expanded
    change eval H (F3J_SamplerRun.program (F3J_InputRows.proof p (decodeState root) w bound) 0 25 P)=_ at expanded
    simp only [expanded]
    rw [← len]
    change (initPair init::callLog c)++(eval H (F3J_SamplerRun.program pf 1 cs.length next)).1=_ ∧ _
    refine ⟨?_,result.2⟩
    rw [result.1]
    rfl

#print axioms sampler
end AspisR1.F3J_First25
end
