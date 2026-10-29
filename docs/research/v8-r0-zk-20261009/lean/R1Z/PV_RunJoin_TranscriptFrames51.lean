import R1Z.PV_RunJoin_TranscriptAbsorb51
import R1Z.PV_RunJoin_TranscriptByteWords51
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_TranscriptFrames51
open Aeneas Aeneas.Std
open ProverCommitOwnerBytes42 (byte)
open ProverRwOuterFrames (flatten)
open PV_RunJoin_TranscriptRequests51 (Block)

theorem message (s : Block) (mark : U8) :
    flatten (PV_RunJoin_TranscriptRequests51.message s mark)=s.val.map byte++[byte mark] := by
  unfold flatten
  rw [PV_RunJoin_TranscriptRequests51.message_bytes,List.map_append,List.map_cons,List.map_nil]

theorem absorb (s : Block) (row : U8) (payload : Slice U8) (small : payload.length≤U32.max) :
    flatten (PV_RunJoin_TranscriptAbsorb51.request s row payload)=
      s.val.map byte++([0,160+byte row]++TranscriptR1.le32 payload.length++payload.val.map byte) := by
  unfold flatten
  rw [PV_RunJoin_TranscriptAbsorb51.bytes]
  simp only [List.map_append,List.map_cons,List.map_nil,PV_RunJoin_TranscriptByteWords51.word,
    PV_RunJoin_TranscriptByteWords51.tag,List.append_assoc]
  rw [PV_RunJoin_TranscriptByteWords51.cast32 (Slice.len payload) small]
  rfl
#print axioms message
#print axioms absorb
end R1Z.PV_RunJoin_TranscriptFrames51
