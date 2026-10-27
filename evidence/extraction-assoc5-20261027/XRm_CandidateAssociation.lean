import XRm_Tx1Cuts
import XRm_CheckpointCalls
open Aeneas Aeneas.Std Result
open XRk_Release XRk_FieldExternal
namespace XRm_CandidateAssociation
/-- SAME accepted emitted TX1: compact guards, canonical scratch and exact
checkpoint MODEL payload/digest cuts. Native parsing/authentication/expansion,
physical heap and attempted-call trace correspondence remain obligations. -/
theorem source {H : Type} (D : aspis_core.digest.Digest32 H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (physical proof : Slice U8) (split : Usize) (hash : H)
    (obs : Option (verifier.Phase → Result Unit)) (out : alloc.vec.Vec U8)
    (run : verifier.candidate.tx1 D pub physical proof split hash obs=ok (.Ok out)) :
    ∃ (p : verifier.Prepared) (scratch : Array XRk_Wide 29#usize) (zero : XRk_Wide)
      (a : verifier.Accumulator),
      verifier.candidate.parse_shape proof=ok (.Ok .S2) ∧
      verifier.candidate.canonical_scan proof=ok (.Ok ()) ∧ split=compact.SPLIT ∧
      aspis_core.field.wide_exact.WideExact.ZERO=ok zero ∧
      verifier.candidate.prepare D pub proof hash obs (Array.repeat 29#usize zero)=ok (.Ok p,scratch) ∧
      (∀ e ∈ scratch.val, XRm_WideProducer.Canonical e) ∧
      ∃ proofHash publicHash wideBytes payload checksum,
        XRk_digest D hash [proof]=ok proofHash ∧ XRk_digest D hash [physical]=ok publicHash ∧
        XRk_asSlice (XRm_CheckpointCalls.bytes p a proofHash publicHash wideBytes)=ok payload ∧
        XRk_digest D hash [XRm_CheckpointCalls.label,payload]=ok checksum ∧
        out.val=payload.val++checksum.val := by
  obtain ⟨p,scratch,zero,a,shape,hshape,hs2,hscan,hzero,hprepare,hsplit,hpowers,canonical,hcheckpoint⟩ :=
    XRm_Tx1Cuts.cuts D pub physical proof split hash obs out run
  subst shape
  obtain ⟨ph,puh,wide,payload,checksum,hph,hpuh,_,hp,hchecksum,hout⟩ :=
    XRm_CheckpointCalls.calls D p a proof physical hash out hcheckpoint
  exact ⟨p,scratch,zero,a,hshape,hscan,hsplit,hzero,hprepare,canonical,
    ph,puh,wide,payload,checksum,hph,hpuh,hp,hchecksum,hout⟩
#print axioms source
end XRm_CandidateAssociation
