import F3J_SemanticValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3J_PositiveTrace
open Aeneas Aeneas.Std Result FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisR1PublicPreparation SourceDigestAddresses SourceDigestLog

def program {Hash : Type} {D : aspis_core.Digest32 Hash} {pre : r1_wire.Prefix} :
    (row : Nat) → (P : LiteralTranscript.Prefix) → (cs : List (SourceFull25.Call D pre)) →
    (bound : ∀ c ∈ cs,(rawBytes c.record.framed).length≤SelectedTranscriptParams.D) →
    Program Bytes State LiteralTranscript.Prefix
  | _,P,[],_ => .done P
  | row,P,c::cs,bound =>
    let m : LiteralTranscript.Message := .payload ⟨rawBytes c.record.framed,bound c (List.mem_cons_self)⟩
    bind (LiteralByteSampler.samp row P m).toProgram fun challenge =>
      program (row+1) (P.ext m challenge) cs (fun d hd => bound d (List.mem_cons_of_mem _ hd))

theorem exact_trace {Hash : Type} {D : aspis_core.Digest32 Hash} {pre : r1_wire.Prefix}
    {before after : r1_wire.SemanticTranscript Hash} {cs : List (SourceFull25.Call D pre)}
    (trace : SourceFull25.Trace D pre before after cs)
    (H : Bytes → State) (backend : Tx1DigestLog.ByteOracleBackend D H)
    (bound : ∀ c ∈ cs,(rawBytes c.record.framed).length≤SelectedTranscriptParams.D)
    (row : Nat) (P : LiteralTranscript.Prefix) (positive : row≠0) (count : row+cs.length≤25)
    (number : before.next_row.val=row)
    (state : UnifiedSampler.stateOf SelectedTranscriptParams.params (LiteralTranscript.erasePrefix P)=decodeState before.state) :
    eval H (program row P cs bound)=
      (sourceLog cs,SourceLiteralTraceLift.sourcePrefix row P cs bound) ∧
    UnifiedSampler.stateOf SelectedTranscriptParams.params
      (LiteralTranscript.erasePrefix (SourceLiteralTraceLift.sourcePrefix row P cs bound))=decodeState after.state := by
  induction trace generalizing row P with
  | nil self => exact ⟨rfl,state⟩
  | @cons after cs c tail ih =>
    have rowC : c.row.val=row := by
      rw [← c.record_row,c.before_row,number]
    have nextC : c.after.next_row.val=row+1 := by
      rw [c.carried]
      change c.next.val=row+1
      rw [c.next_row,c.record_row,rowC]
    let m : LiteralTranscript.Message := .payload ⟨rawBytes c.record.framed,bound c (List.mem_cons_self)⟩
    have step := F3J_SemanticValue.payload c H backend row positive (by simp only [List.length_cons] at count; omega)
      rowC P m ⟨rawBytes c.record.framed,bound c (List.mem_cons_self)⟩ rfl state rfl
    let next := P.ext m (.ordinary (SourceLiteralTraceLift.sourceChallenge c),decodeState c.after.state)
    have nextState : UnifiedSampler.stateOf SelectedTranscriptParams.params
        (LiteralTranscript.erasePrefix next)=decodeState c.after.state := by
      dsimp only [next]
      rw [LiteralTranscript.erasePrefix_ext,UnifiedSampler.stateOf_ext]
    have result := ih (fun d hd => bound d (List.mem_cons_of_mem _ hd)) (row+1) next (by omega)
      (by simp only [List.length_cons] at count; omega) nextC nextState
    constructor
    · change eval H (bind (LiteralByteSampler.samp row P m).toProgram
        (fun ch => program (row+1) (P.ext m ch) cs _))=_
      rw [eval_bind,step]
      change (callLog c++(eval H (program (row+1) next cs _)).1,
        (eval H (program (row+1) next cs _)).2)=_
      rw [result.1]
      rfl
    · exact result.2

#print axioms exact_trace
end AspisR1.F3J_PositiveTrace
end
