import R1Z.PV_RunJoin_TranscriptRequests51
set_option autoImplicit false
namespace R1Z.PV_RunJoin_TranscriptAbsorb51
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_TranscriptRequests51 (Block)

def request (s : Block) (row : U8) (payload : Slice U8) : Slice (Slice U8) :=
  Array.to_slice (Array.make 4#usize [Array.to_slice s,
    Array.to_slice (Array.make 2#usize [0#u8,U8.wrapping_add 160#u8 row]),
    Array.to_slice (core.num.U32.to_le_bytes (UScalar.cast .U32 (Slice.len payload))),payload])

theorem source [ExternalTypes] {H : Type} (D : aspis_core.digest.Digest32 H)
    (t : host_transcript.Transcript H) (row : U8) (payload : Slice U8) :
    host_transcript.Transcript.absorb D t row payload=(do
      let s ← D.digest t.hash (request t.state row payload)
      ok {t with state:=s}) := by
  simp only [host_transcript.Transcript.absorb,request,lift,bind_tc_ok]

theorem bytes (s : Block) (row : U8) (payload : Slice U8) :
    (request s row payload).val.flatMap (fun x => x.val)=
      s.val++[0#u8,U8.wrapping_add 160#u8 row]++
      (core.num.U32.to_le_bytes (UScalar.cast .U32 (Slice.len payload))).val++payload.val := by
  simp only [request,Array.to_slice,Array.make,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc]
#print axioms request
#print axioms source
#print axioms bytes
end R1Z.PV_RunJoin_TranscriptAbsorb51
