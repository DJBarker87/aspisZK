import NDO_JHn_AuthRanges

import NDO_JHn_ContentRanges
import NDO_JHn_BodyHeader
import NDO_JHl_KnownFields
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHn_BodyIdentity
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open JHe_CurrentWriterImage
attribute [local irreducible] JFx_NativeBytes.checkpoint JFx_NativeBytes.checkpointBytes
/-- Full body identity from named field identities, with no buffer reduction. -/
theorem source (p : verifier.Prepared) (a : verifier.Accumulator)
    (hp hu : Array U8 32#usize) (fields : JHl_KnownFields.Fields p a)
    (claim : (WAdm_SourceBody.put (prepared p).claim).map CheckpointBytes5Writer.u8=JFq_Claim.bytes)
    (proofDigest : hp=JFq_AuthBytes.proofHash) (publicDigest : hu=JFq_AuthBytes.publicHash)
    (variant : p.variant=.S2) (next : a.next.val=10) :
    (WAdm_SourceBody.body (prepared p) (accumulator a) hp hu).map CheckpointBytes5Writer.u8=
      JFx_NativeBytes.checkpoint.val.take 1736 := by
  have pv : (prepared p).variant=.S2 := by
    change CheckpointBytes3Namespaces.toVariant (Tx1Q_Carriers.variant p.variant)=_
    rw [variant]
    rfl
  have an : (accumulator a).next.val=10 := next
  unfold WAdm_SourceBody.body
  simp only [List.map_append]
  rw [JHn_BodyHeader.source _ _ pv an,WAdm_SourceWriter.map_bytes,WAdm_SourceWriter.map_bytes,
    proofDigest,publicDigest,fields.inherited.fixed.1,fields.inherited.fixed.2.1,
    fields.inherited.early.1,fields.inherited.early.2.1,fields.inherited.early.2.2.1,
    fields.inherited.early.2.2.2,fields.inherited.fixed.2.2,fields.semantic,fields.z,
    claim,fields.inherited.rhs,fields.inherited.power,fields.weights]
  have pref :=  JHn_AuthRanges.source
  have body := JHn_ContentRanges.source
  rw [show JFx_NativeBytes.checkpoint.val.take 16=WAdm_FissionedContent.header from JFq_AuthBytes.first16,pref]
  simp only [List.append_assoc] at body ⊢
  rw [body]
  simpa only [List.drop_zero] using JHn_Ranges.adjacent JFx_NativeBytes.checkpoint.val 0 80 1656
#print axioms source
end AspisR1.JHn_BodyIdentity
end
