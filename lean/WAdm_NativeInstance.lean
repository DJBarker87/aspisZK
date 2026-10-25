import WAdm_FissionedRoot
import WAdm_FissionedFields
import WAdm_SourceWriter
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.WAdm_NativeInstance
open WAdm_Fissioned WAdm_model
open OraclePortCkptAbi2Extracted.aspis_r1_cost_probe.verifier
open CheckpointBytes5Effect CheckpointBytes3Namespaces
open AspisR1Stage2.WireTx2 (checksumParts)

/-- Concrete emitted source invocation for the paired, bounded native
certificate, with the original Prepared/Accumulator and slice inputs. -/
def native {H : Type} (D : WAdm_Fissioned.aspis_core.digest.Digest32 H)
    (p : Prepared) (a : Accumulator) (proof pub : Slice U8) (hash : H) : Result (alloc.vec.Vec U8) := do
  let f ← WAdm_fields p a.rhs a.power
  WAdm_checkpoint D f a.weights proof pub hash

attribute [local irreducible] CheckpointBytesDecodeC5.sourceBody WAdm_FissionedContent.body

theorem raw_body (p : Prepared) (a : Accumulator) (hp hu : Array U8 32#usize)
    (size : a.weights.val.length = 64)
    (qb : ∀ j : Fin 22, (p.queries.val[j.val]'(by simpa [p.queries.property] using j.isLt)).val < 262144)
    (canonical : CheckpointBytesBlocks.CanonicalFields (CheckpointBytesBody.fields p a size qb))
    (variant : p.variant = .S2) (next : a.next.val = 10) :
    WAdm_FissionedContent.body (WAdm_FissionedFields.fields p a) a.weights hp hu =
      (CheckpointBytesDecodeC5.sourceBody p a hp hu).map CheckpointBytes5Writer.u8 := by
  have h := congrArg (List.map CheckpointBytes5Writer.u8)
    (WAdm_FissionedFields.body_bytes p a hp hu variant next)
  rw [WAdm_SourceWriter.map_bytes,WAdm_BodyJoin.selector p a hp hu size qb canonical variant next] at h
  exact h

theorem body_slice (p : Prepared) (a : Accumulator) (hp hu : Array U8 32#usize)
    (size : a.weights.val.length = 64)
    (qb : ∀ j : Fin 22, (p.queries.val[j.val]'(by simpa [p.queries.property] using j.isLt)).val < 262144)
    (canonical : CheckpointBytesBlocks.CanonicalFields (CheckpointBytesBody.fields p a size qb))
    (variant : p.variant = .S2) (next : a.next.val = 10) :
    WAdm_FissionedContent.bodySlice (WAdm_FissionedFields.fields p a) a.weights hp hu size =
      CheckpointBytes5Writer.bodySlice p a hp hu := by
  apply Subtype.ext
  exact raw_body p a hp hu size qb canonical variant next

theorem raw_accepted {H : Type} (D : WAdm_Fissioned.aspis_core.digest.Digest32 H) (hash : H)
    (p : Prepared) (a : Accumulator) (proof pub ck : Slice U8)
    (size : a.weights.val.length = 64)
    (qb : ∀ j : Fin 22, (p.queries.val[j.val]'(by simpa [p.queries.property] using j.isLt)).val < 262144)
    (canonical : CheckpointBytesBlocks.CanonicalFields (CheckpointBytesBody.fields p a size qb))
    (variant : p.variant = .S2) (next : a.next.val = 10)
    (reference : erase D hash (CheckpointBytes5Writer.writer p a proof pub) = ok ck) :
    native D p a proof pub hash = ok ⟨ck.val,ck.property⟩ := by
  simp only [CheckpointBytes5Writer.writer,erase_bind,erase_read,erase_pure] at reference
  obtain ⟨hp,hpCall,tail⟩ := Port3_PushFrame.bind_success _ _ _ reference
  obtain ⟨hu,huCall,tail⟩ := Port3_PushFrame.bind_success _ _ _ tail
  obtain ⟨hc,hcCall,tail⟩ := Port3_PushFrame.bind_success _ _ _ tail
  have same := Result.ok.inj tail
  subst ck
  have checksum : D.digest hash
      (checksumParts (WAdm_FissionedContent.bodySlice (WAdm_FissionedFields.fields p a) a.weights hp hu size)) = ok hc := by
    rw [body_slice p a hp hu size qb canonical variant next]
    exact hcCall
  have actual := WAdm_FissionedRoot.emitted D hash (WAdm_FissionedFields.fields p a) a.weights
    proof pub size hp hu hc hpCall huCall checksum
  have final : WAdm_FissionedContent.finish (WAdm_FissionedFields.fields p a) a.weights hp hu hc size =
      (⟨(CheckpointBytes5Writer.finish p a hp hu hc).val,(CheckpointBytes5Writer.finish p a hp hu hc).property⟩ : alloc.vec.Vec U8) := by
    apply Subtype.ext
    change WAdm_FissionedContent.body (WAdm_FissionedFields.fields p a) a.weights hp hu ++ hc.val = _
    rw [raw_body p a hp hu size qb canonical variant next]
    rfl
  unfold native
  rw [WAdm_FissionedFields.returned,bind_tc_ok]
  exact actual.trans (congrArg Result.ok final)

def writer {H : Type} (D : VTop_Stages.aspis_core.digest.Digest32 H)
    (p : AspisR1Stage2.verifier.Prepared) (a : AspisR1Stage2.verifier.Accumulator)
    (proof pub : Slice U8) (hash : H) : Result (alloc.vec.Vec U8) :=
  native (VTop_Checkpoint.digest D) (toPrepared p) (toAccumulator a) proof pub hash

theorem accepted {H : Type} (D : VTop_Stages.aspis_core.digest.Digest32 H)
    (p : AspisR1Stage2.verifier.Prepared) (a : AspisR1Stage2.verifier.Accumulator)
    (proof pub : Slice U8) (hash : H) (saved : alloc.vec.Vec U8)
    (fields : Port5Q2_Prepared.PreparedFields p) (size : a.weights.val.length = 64)
    (canonical : CheckpointBytesBlocks.CanonicalFields (Port3_DecodeCoherence.inventory p a size fields.queries))
    (next : a.next.val = 10)
    (reference : Port3_CheckpointInstall.writer D p a proof pub hash = ok saved) :
    writer D p a proof pub hash = ok saved := by
  unfold Port3_CheckpointInstall.writer at reference
  obtain ⟨ck,call,returned⟩ := Port3_PushFrame.bind_success _ _ _ reference
  have same := Result.ok.inj returned
  subst saved
  apply raw_accepted (VTop_Checkpoint.digest D) hash (toPrepared p) (toAccumulator a) proof pub ck
    (by simpa only [toAccumulator,mapVec,List.length_map] using size) fields.queries canonical
  · change toVariant p.variant = _
    rw [fields.variant]
    rfl
  · exact next
  · exact call

#print axioms raw_body
#print axioms body_slice
#print axioms raw_accepted
#print axioms accepted
end AspisR1.WAdm_NativeInstance
end
