import R1Z.PV_RunJoin_TranscriptRequests51
import R1Z.ProverRwOuterTag
set_option autoImplicit false
namespace R1Z.PV_RunJoin_TranscriptReseedSource51
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_TranscriptRequests51 (Block)

def domain : Slice U8 := Array.to_slice (Array.make 29#usize [
  85#u8,78#u8,80#u8,82#u8,79#u8,86#u8,69#u8,68#u8,58#u8,82#u8,
  49#u8,58#u8,80#u8,82#u8,73#u8,86#u8,65#u8,84#u8,69#u8,45#u8,
  83#u8,65#u8,76#u8,84#u8,69#u8,68#u8,58#u8,80#u8,51#u8])

def request (semantic : Block) (tag : U8) : Slice (Slice U8) :=
  Array.to_slice (Array.make 3#usize [domain,Array.to_slice (Array.make 1#usize [tag]),Array.to_slice semantic])

theorem source [ExternalTypes] [ExternalFuns] {H : Type} (D : aspis_core.digest.Digest32 H)
    (hash : H) (semantic : Block) (variant : transport.Variant) :
    host_transcript.Transcript.new D hash semantic variant=(do
      let tag ← transport.Variant.tag variant
      let state ← D.digest hash (request semantic tag)
      ok ⟨state,hash⟩) := by
  simp only [host_transcript.Transcript.new,request,domain,lift,bind_tc_ok]
#print axioms domain
#print axioms request
#print axioms source
end R1Z.PV_RunJoin_TranscriptReseedSource51
