import XRm_CheckpointCalls
open Aeneas Aeneas.Std Result
open XRk_Release XRk_FieldExternal XRk_ResultTools
namespace XRm_CheckpointSize
theorem finish_length (bs : List U8) (checksum : Array U8 32#usize) (size : Nat)
    (out : alloc.vec.Vec U8) (run : XRm_CheckpointFinalize.finish bs checksum size=ok out) :
    out.val.length=size := by
  unfold XRm_CheckpointFinalize.finish at run
  split_ifs at run with valid
  · have bytes := XRm_CheckpointCalls.slice _ out run
    rw [bytes]
    exact valid

/-- Isolate the model's final size guard with fully specified arguments;
no normalization of the complete serialized prefix is needed. -/
theorem model {H : Type} (D : aspis_core.digest.Digest32 H)
    (p : verifier.Prepared) (a : verifier.Accumulator) (proof pub : Slice U8) (hash : H)
    (out : alloc.vec.Vec U8) (run : verifier.checkpoint D p a proof pub hash=ok out) :
    out.val.length=(if p.variant matches .S1 then 4840 else 1768) := by
  unfold verifier.checkpoint at run
  obtain ⟨ph,_,run⟩ := bind_success _ _ _ run
  obtain ⟨puh,_,run⟩ := bind_success _ _ _ run
  obtain ⟨wide,_,run⟩ := bind_success _ _ _ run
  obtain ⟨payload,_,run⟩ := bind_success _ _ _ run
  obtain ⟨checksum,_,run⟩ := bind_success _ _ _ run
  exact finish_length (XRm_CheckpointCalls.bytes p a ph puh wide) checksum _ out run
#print axioms finish_length
#print axioms model
end XRm_CheckpointSize
