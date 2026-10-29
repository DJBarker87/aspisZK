import R1Z.PV_RunJoin_PrepareReach50
set_option autoImplicit false
namespace R1Z.PV_RunJoin_TranscriptRequests51
open Aeneas Aeneas.Std Result ProverRwFull
abbrev Block := Array U8 32#usize

def message (s : Block) (mark : U8) : Slice (Slice U8) :=
  Array.to_slice (Array.make 2#usize [Array.to_slice s,
    Array.to_slice (Array.make 1#usize [mark])])

theorem message_bytes (s : Block) (mark : U8) :
    (message s mark).val.flatMap (fun x => x.val)=s.val++[mark] := by
  simp only [message,Array.to_slice,Array.make,List.flatMap_cons,List.flatMap_nil,List.append_nil]

theorem block [ExternalTypes] {H : Type} (D : aspis_core.digest.Digest32 H)
    (t : host_transcript.Transcript H) (row : U8) (payload : Slice U8) :
    host_transcript.Transcript.block D t row payload=(do
      let next ← host_transcript.Transcript.absorb D t row payload
      let b ← D.digest next.hash (message next.state 1#u8)
      let s ← D.digest next.hash (message next.state 2#u8)
      ok (b,{next with state:=s})) := by
  simp only [host_transcript.Transcript.block,message,lift,bind_tc_ok]
#print axioms message
#print axioms message_bytes
#print axioms block
end R1Z.PV_RunJoin_TranscriptRequests51
