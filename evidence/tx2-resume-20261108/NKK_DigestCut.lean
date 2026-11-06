import NJU_ResumeObserved
set_option autoImplicit false
noncomputable section
namespace NKK_DigestCut
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission

def Domain (stored proof : Slice U8) : Prop :=
 stored.val.length=32 ∧ proof.val.length=57607

/-- Logical transcription of proof_digest_frame_cut, native proof_for_contract
NKK_K042/046/047 (source pins in NKK_CERTIFICATES; supplementary argument control pending). Result is the literal
comparison; exact modifies excludes the proof/stored bytes and reply buffer.
Pointer/length observations identify the borrowed carrier; byte identity here
comes from the checked full modifies frame, not pointer equality alone. -/
structure Cut (stored proof : Slice U8) (reply : Array U8 32#usize)
 (postStored postProof : Slice U8) (postReply : Array U8 32#usize)
 (out : core.result.Result Unit verifier.Error) : Prop where
 proof_frame : postProof=proof
 stored_frame : postStored=stored
 reply_frame : postReply=reply
 result : out=if stored.val=reply.val then .Ok () else .Err .Checkpoint

/-- Instantiating the digest reply at this event preserves both input views
and the full rejection arm. No digest-value law is added. -/
theorem same_call (stored proof : Slice U8) (reply : Array U8 32#usize)
 (postStored postProof : Slice U8) (postReply : Array U8 32#usize)
 (out : core.result.Result Unit verifier.Error)
 (cut : Cut stored proof reply postStored postProof postReply out) :
 postProof=proof ∧ postStored=stored ∧ postReply=reply ∧
 out=(if stored.val=reply.val then .Ok () else .Err .Checkpoint) :=
 ⟨cut.proof_frame,cut.stored_frame,cut.reply_frame,cut.result⟩

/-- Byte-frame consequence of the checked modifies set at any index,
including every byte of the57607-byte proof, with no reduction/unrolling. -/
theorem byte_frame (stored proof : Slice U8) (reply : Array U8 32#usize)
 (postStored postProof : Slice U8) (postReply : Array U8 32#usize)
 (out : core.result.Result Unit verifier.Error)
 (cut : Cut stored proof reply postStored postProof postReply out) (i : Nat) :
 postProof.val[i]?=proof.val[i]? := by rw [cut.proof_frame]

#print axioms same_call
#print axioms byte_frame
end NKK_DigestCut
