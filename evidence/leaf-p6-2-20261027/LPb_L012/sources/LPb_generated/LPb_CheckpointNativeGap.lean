import LPb_ResultInversion
open Aeneas Aeneas.Std Result
open XRk_Release XRk_FieldExternal
open LPb_CheckpointLayout LPb_CheckpointSequence LPb_ResultInversion
namespace LPb_CheckpointNativeGap
/-- All witnesses come from ONE supplied checkpoint-model execution.
The name marks the still-open native bridge; this is not that bridge. -/
theorem model_trace_bytes {H : Type} (D : aspis_core.digest.Digest32 H)
    (p : verifier.Prepared) (a : verifier.Accumulator) (proof pub : Slice U8) (hash : H)
    (out : alloc.vec.Vec U8) (run : verifier.checkpoint D p a proof pub hash = ok out) :
    ∃ ph uh ws payload checksum,
      XRk_digest D hash [proof] = ok ph ∧
      XRk_digest D hash [pub] = ok uh ∧
      wideStages p a = ok ws ∧
      XRk_asSlice (bytes p a ph uh ws) = ok payload ∧
      XRk_digest D hash [label,payload] = ok checksum ∧
      logged D p a proof pub hash = ([[proof],[pub],[label,payload]],ok out) ∧
      out.val = payload.val ++ checksum.val := by
  rw [checkpoint_model_stages] at run
  unfold LPb_CheckpointSequence.sequence at run
  obtain ⟨ph,hph,run⟩ := bind_success _ _ _ run
  obtain ⟨uh,huh,run⟩ := bind_success _ _ _ run
  obtain ⟨ws,hws,run⟩ := bind_success _ _ _ run
  obtain ⟨payload,hpayload,run⟩ := bind_success _ _ _ run
  obtain ⟨checksum,hchecksum,run⟩ := bind_success _ _ _ run
  have final := run
  have tr := LPb_CheckpointAttempts.successful_stages D p a proof pub hash ph uh checksum ws payload out
    hph huh hws hpayload hchecksum final
  have hp := slice_value _ payload hpayload
  refine ⟨ph,uh,ws,payload,checksum,hph,huh,hws,hpayload,hchecksum,tr,?_⟩
  unfold lastStage at run
  split at run
  · have hout := slice_value _ out run
    rw [hp]
    exact hout
  · cases run
#print axioms model_trace_bytes
end LPb_CheckpointNativeGap
