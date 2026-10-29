import R1Z.PV_RunJoin_TranscriptFrames51
set_option autoImplicit false
namespace R1Z.PV_RunJoin_SemanticRequests51
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_TranscriptRequests51 (Block message)

def request (state : Block) (row : U8) (framed : Slice U8) : Slice (Slice U8) :=
  Array.to_slice (Array.make 3#usize [Array.to_slice state,
    Array.to_slice (Array.make 2#usize [0#u8,U8.wrapping_add 160#u8 row]),framed])

theorem source [ExternalTypes] {H : Type} (D : aspis_core.digest.Digest32 H)
    (t : host_wire.SemanticTranscript H) (row : U8) (framed : Slice U8) :
    host_wire.SemanticTranscript.sample_block_validated D t row framed=
      if row!=t.next_row then ok (.Err (.RowOrder t.next_row row),t) else (do
        let absorbed ← D.digest t.hash (request t.state row framed)
        let b ← D.digest t.hash (message absorbed 1#u8)
        let advanced ← D.digest t.hash (message absorbed 2#u8)
        ok (.Ok b,{t with state:=advanced,next_row:=U8.wrapping_add t.next_row 1#u8})) := by
  simp only [host_wire.SemanticTranscript.sample_block_validated,request,message,lift,bind_tc_ok]

theorem frame (s : Block) (row : U8) (framed : Slice U8) :
    ProverRwOuterFrames.flatten (request s row framed)=s.val.map ProverCommitOwnerBytes42.byte++
      ([0,160+ProverCommitOwnerBytes42.byte row]++framed.val.map ProverCommitOwnerBytes42.byte) := by
  simp only [ProverRwOuterFrames.flatten,request,Array.to_slice,Array.make,List.flatMap_cons,
    List.flatMap_nil,List.append_nil,List.map_append,List.map_cons,List.map_nil,
    PV_RunJoin_TranscriptByteWords51.tag,List.append_assoc]
  rfl
#print axioms request
#print axioms source
#print axioms frame
end R1Z.PV_RunJoin_SemanticRequests51
