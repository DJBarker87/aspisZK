import RPz7_F3J_SemanticLog
import RPz7_S1SemanticCodeSampleBlockExactV1
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3J_BlockCalls
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge

structure Calls {Hash : Type} (D : aspis_core.Digest32 Hash)
    (before after : r1_wire.SemanticTranscript Hash) (row : U8) (framed : Slice U8)
    (block : Array U8 32#usize) where
  tag : U8
  next : U8
  absorbed : Array U8 32#usize
  state : Array U8 32#usize
  row_eq : row=before.next_row
  tag_value : tag.val=160+row.val
  next_value : next.val=row.val+1
  absorb : D.digest before.hash (TranscriptStep.absorbParts before.state tag framed)=ok absorbed
  squeeze : D.digest before.hash (TranscriptStep.readParts absorbed 1#u8)=ok block
  advance : D.digest before.hash (TranscriptStep.readParts absorbed 2#u8)=ok state
  carried : after={before with state,next_row:=next}

def log {Hash : Type} {D : aspis_core.Digest32 Hash}
    {before after : r1_wire.SemanticTranscript Hash} {row : U8} {framed : Slice U8}
    {block : Array U8 32#usize} (c : Calls D before after row framed block) : List (Bytes × State) :=
  [(flatten (TranscriptStep.absorbParts before.state c.tag framed),decodeState c.absorbed),
   (flatten (TranscriptStep.readParts c.absorbed 1#u8),decodeState block),
   (flatten (TranscriptStep.readParts c.absorbed 2#u8),decodeState c.state)]

theorem from_success {Hash : Type} (D : aspis_core.Digest32 Hash)
    (before after : r1_wire.SemanticTranscript Hash) (row : U8) (framed : Slice U8)
    (block : Array U8 32#usize) (below : row.val≤26)
    (success : r1_wire.SemanticTranscript.sample_block_validated D before row framed=ok (.Ok block,after)) :
    Nonempty (Calls D before after row framed block) := by
  obtain ⟨rowEq,tag,next,absorbed,state,tagValue,nextValue,ha,hb,hs,carried⟩ :=
    TranscriptStep.step_success D before after row framed block below success
  exact ⟨⟨tag,next,absorbed,state,rowEq,tagValue,nextValue,ha,hb,hs,carried⟩⟩

theorem consistent {Hash : Type} {D : aspis_core.Digest32 Hash}
    {before after : r1_wire.SemanticTranscript Hash} {row : U8} {framed : Slice U8}
    {block : Array U8 32#usize} (c : Calls D before after row framed block)
    (H : Bytes → State) (backend : Tx1DigestLog.ByteOracleBackend D H) :
    ∀ q ∈ log c,q.2=H q.1 := by
  intro q hq
  simp only [log,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl|rfl|rfl
  · exact backend _ ⟨before.hash,_,c.absorbed,rfl,c.absorb⟩
  · exact backend _ ⟨before.hash,_,block,rfl,c.squeeze⟩
  · exact backend _ ⟨before.hash,_,c.state,rfl,c.advance⟩

#print axioms from_success
#print axioms consistent
end AspisR1.F3J_BlockCalls
end
