import F3J_SamplerRun
import F3J_SemanticValue
import F3J_RowBindings
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3J_SemanticPrefix
open Aeneas Aeneas.Std Result FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisR1PublicPreparation SourceDigestAddresses SourceDigestLog
open OraclePortCompactDraft

theorem positive {Hash : Type} {D : aspis_core.Digest32 Hash} {pre : r1_wire.Prefix}
    {before after : r1_wire.SemanticTranscript Hash} {cs : List (SourceFull25.Call D pre)}
    (trace : SourceFull25.Trace D pre before after cs)
    (H : Bytes → State) (backend : Tx1DigestLog.ByteOracleBackend D H)
    (p : Parsed) (records : p.semantic=pre.records.val.map (fun s => MultiproofConeCanonical.bytesOf s.val))
    (root : State) (w : CanonicalCutEnrichedTranscript.Words)
    (bound : ∀ row,(rowBytes p row).length≤SelectedTranscriptParams.D)
    (row : Nat) (P : LiteralTranscript.Prefix) (positive : row≠0) (count : row+cs.length≤25)
    (number : before.next_row.val=row)
    (state : UnifiedSampler.stateOf SelectedTranscriptParams.params (LiteralTranscript.erasePrefix P)=decodeState before.state) :
    let pf := F3J_InputRows.proof p root w bound
    (eval H (F3J_SamplerRun.program pf row cs.length P)).1=sourceLog cs ∧
      UnifiedSampler.stateOf SelectedTranscriptParams.params
        (LiteralTranscript.erasePrefix (eval H (F3J_SamplerRun.program pf row cs.length P)).2)=decodeState after.state := by
  dsimp only
  induction trace generalizing row P with
  | nil self => exact ⟨rfl,state⟩
  | @cons after cs c tail ih =>
    have rowC : c.row.val=row := by rw [← c.record_row,c.before_row,number]
    have nextC : c.after.next_row.val=row+1 := by
      rw [c.carried]
      change c.next.val=row+1
      rw [c.next_row,c.record_row,rowC]
    let pf := F3J_InputRows.proof p root w bound
    have erased : LiteralTranscript.erase (pf row)=.payload ⟨rowBytes p row,bound row⟩ := by
      rw [F3J_InputRows.erased,if_neg positive]
    have bytesEq : rowBytes p row=rawBytes c.record.framed := by
      rw [← rowC]
      exact F3J_RowBindings.payload c p records (by simp only [List.length_cons] at count; omega)
    have step := F3J_SemanticValue.payload c H backend row positive
      (by simp only [List.length_cons] at count; omega) rowC P (pf row)
      ⟨rowBytes p row,bound row⟩ erased state bytesEq
    let next := P.ext (pf row) (.ordinary (SourceLiteralTraceLift.sourceChallenge c),decodeState c.after.state)
    have nextState : UnifiedSampler.stateOf SelectedTranscriptParams.params
        (LiteralTranscript.erasePrefix next)=decodeState c.after.state := by
      dsimp only [next]
      rw [LiteralTranscript.erasePrefix_ext,UnifiedSampler.stateOf_ext]
    have result := ih (row+1) next (by omega)
      (by simp only [List.length_cons] at count; omega) nextC nextState
    change (eval H (F3J_SamplerRun.program pf row (cs.length+1) P)).1=_ ∧ _
    rw [F3J_SamplerRun.program,eval_bind,step]
    exact ⟨by rw [result.1];rfl,result.2⟩

#print axioms positive
end AspisR1.F3J_SemanticPrefix
end
