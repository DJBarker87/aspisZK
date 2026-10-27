import XRm_CheckpointLayout
open Aeneas Aeneas.Std Result
open XRk_Release XRk_FieldExternal XRk_ResultTools
namespace XRm_CheckpointCalls
theorem calls {H : Type} (D : aspis_core.digest.Digest32 H)
    (p : verifier.Prepared) (a : verifier.Accumulator) (proof pub : Slice U8) (hash : H)
    (out : alloc.vec.Vec U8) (run : verifier.checkpoint D p a proof pub hash=ok out) :
    ∃ proofHash publicHash wideBytes payload checksum,
      XRk_digest D hash [proof]=ok proofHash ∧ XRk_digest D hash [pub]=ok publicHash ∧
      [p.gamma,p.kappa,p.alpha.val[0]?.getD p.gamma,p.alpha.val[1]?.getD p.gamma,p.claim,a.rhs].mapM
        aspis_core.field.wide_exact.WideExact.to_le_bytes=ok wideBytes ∧
      XRk_asSlice (bytes p a proofHash publicHash wideBytes)=ok payload ∧
      XRk_digest D hash [label,payload]=ok checksum ∧
      out.val=payload.val++checksum.val := by
  unfold verifier.checkpoint at run
  obtain ⟨proofHash,hproof,run⟩ := bind_success _ _ _ run
  obtain ⟨publicHash,hpublic,run⟩ := bind_success _ _ _ run
  obtain ⟨wideBytes,hwide,run⟩ := bind_success _ _ _ run
  obtain ⟨payload,hpayload,run⟩ := bind_success _ _ _ run
  obtain ⟨checksum,hchecksum,run⟩ := bind_success _ _ _ run
  have hbytes : XRk_asSlice (bytes p a proofHash publicHash wideBytes)=ok payload := hpayload
  refine ⟨proofHash,publicHash,wideBytes,payload,checksum,hproof,hpublic,hwide,hbytes,hchecksum,?_⟩
  have hp := slice _ payload hbytes
  split at run
  · have hout := slice _ out run
    rw [hp]
    exact hout
  · cases run
#print axioms slice
#print axioms calls
end XRm_CheckpointCalls
