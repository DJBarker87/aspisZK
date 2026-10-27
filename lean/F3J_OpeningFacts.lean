import F3J_ReseedSource
import PAln_OpeningCalls
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3J_OpeningFacts
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge

structure Calls {Hash : Type} (D : aspis_core.Digest32 Hash)
    (before after : transcript.Transcript Hash) (row : U8) (payload : Slice U8)
    (block : Array U8 32#usize) where
  tag : U8
  absorbed : Array U8 32#usize
  state : Array U8 32#usize
  tag_add : 160#u8+row=ok tag
  absorb : D.digest before.hash (CallerStep.openingAbsorbParts before.state tag
    (UScalar.cast .U32 (Slice.len payload)) payload)=ok absorbed
  squeeze : D.digest before.hash (TranscriptStep.readParts absorbed 1#u8)=ok block
  advance : D.digest before.hash (TranscriptStep.readParts absorbed 2#u8)=ok state
  carried : after={state,hash:=before.hash}

def log {Hash : Type} {D : aspis_core.Digest32 Hash}
    {before after : transcript.Transcript Hash} {row : U8} {payload : Slice U8}
    {block : Array U8 32#usize} (c : Calls D before after row payload block) : List (Bytes × State) :=
  [(flatten (CallerStep.openingAbsorbParts before.state c.tag (UScalar.cast .U32 (Slice.len payload)) payload),decodeState c.absorbed),
   (flatten (TranscriptStep.readParts c.absorbed 1#u8),decodeState block),
   (flatten (TranscriptStep.readParts c.absorbed 2#u8),decodeState c.state)]

theorem from_success {Hash : Type} (D : aspis_core.Digest32 Hash)
    (before after : transcript.Transcript Hash) (row : U8) (payload : Slice U8)
    (block : Array U8 32#usize)
    (success : transcript.Transcript.block D before row payload=ok (block,after)) :
    Nonempty (Calls D before after row payload block) := by
  obtain ⟨absorbed,state,ha,hb,hs,carried⟩ := CallerStep.opening_block_success D before after row payload block success
  obtain ⟨tag,abs,add,digest,absEq⟩ := PAln_OpeningCalls.absorb_success D before absorbed row payload ha
  rw [absEq] at hb hs carried
  exact ⟨⟨tag,abs,state,add,digest,hb,hs,carried⟩⟩

theorem consistent {Hash : Type} {D : aspis_core.Digest32 Hash}
    {before after : transcript.Transcript Hash} {row : U8} {payload : Slice U8}
    {block : Array U8 32#usize} (c : Calls D before after row payload block)
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
end AspisR1.F3J_OpeningFacts
end
