import WAdm_BodyJoin
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.WAdm_SourceWriter
open OraclePortCkptAbi2Extracted aspis_r1_cost_probe.verifier
open CheckpointBytes5Effect CheckpointBytes3Namespaces CheckpointBytesDigest
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep MultiproofConeCanonical
open AspisR1Stage2.WireTx2 (singletonParts checksumParts)

def toSlice (bs : Bytes) : Result (Slice U8) :=
  if h : bs.length ≤ Usize.max then
    ok ⟨bs.map CheckpointBytes5Writer.u8,by simpa only [List.length_map] using h⟩
  else fail .panic

/-- Explicit append-content writer. It retains proof/public/checksum order
and reads the checksum from the body just constructed. This is a content
interpretation; no native heap/allocator refinement is asserted here. -/
def code (p : Prepared) (a : Accumulator) (proof pub : Slice U8) : Code (Slice U8) := do
  let hp ← read (singletonParts proof)
  let hu ← read (singletonParts pub)
  let b := WAdm_SourceBody.body p a hp hu
  let buf ← liftResult (toSlice b)
  let hc ← read (checksumParts buf)
  liftResult (toSlice (b ++ bytesOf hc.val))

attribute [local irreducible] CheckpointBytesDecodeC5.sourceBody WAdm_SourceBody.body

theorem materialize (p : Prepared) (a : Accumulator) (hp hu : Array U8 32#usize)
    (size : a.weights.val.length = 64)
    (qb : ∀ j : Fin 22, (p.queries.val[j.val]'(by simpa [p.queries.property] using j.isLt)).val < 262144)
    (canonical : CheckpointBytesBlocks.CanonicalFields (CheckpointBytesBody.fields p a size qb))
    (variant : p.variant = .S2) (next : a.next.val = 10) :
    toSlice (WAdm_SourceBody.body p a hp hu) = ok (CheckpointBytes5Writer.bodySlice p a hp hu) := by
  rw [WAdm_BodyJoin.selector p a hp hu size qb canonical variant next]
  have size1 : (CheckpointBytesDecodeC5.sourceBody p a hp hu).length = 1736 := by
    rw [CheckpointBytesDecodeC5.sourceBody,List.length_ofFn]
  have bound : (CheckpointBytesDecodeC5.sourceBody p a hp hu).length ≤ Usize.max := by
    rw [size1]
    scalar_tac
  simp only [toSlice,dif_pos bound,CheckpointBytes5Writer.bodySlice]

theorem u8_decode (x : U8) :
    CheckpointBytes5Writer.u8 (AspisV8R19.SqueezeOracleBridge.decodeByte x) = x := by
  apply UScalar.eq_of_val_eq
  rfl

theorem map_bytes (xs : List U8) : (bytesOf xs).map CheckpointBytes5Writer.u8 = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simpa only [bytesOf,List.map_cons,u8_decode] using congrArg (List.cons x) ih

theorem finish (p : Prepared) (a : Accumulator) (hp hu hc : Array U8 32#usize)
    (size : a.weights.val.length = 64)
    (qb : ∀ j : Fin 22, (p.queries.val[j.val]'(by simpa [p.queries.property] using j.isLt)).val < 262144)
    (canonical : CheckpointBytesBlocks.CanonicalFields (CheckpointBytesBody.fields p a size qb))
    (variant : p.variant = .S2) (next : a.next.val = 10) :
    toSlice (WAdm_SourceBody.body p a hp hu ++ bytesOf hc.val) =
      ok (CheckpointBytes5Writer.finish p a hp hu hc) := by
  rw [WAdm_BodyJoin.selector p a hp hu size qb canonical variant next]
  have size1 : (CheckpointBytesDecodeC5.sourceBody p a hp hu).length = 1736 := by
    rw [CheckpointBytesDecodeC5.sourceBody,List.length_ofFn]
  have bound : (CheckpointBytesDecodeC5.sourceBody p a hp hu ++ bytesOf hc.val).length ≤ Usize.max := by
    simp only [List.length_append,size1,bytesOf,List.length_map,hc.property]
    scalar_tac
  simp only [toSlice,dif_pos bound,CheckpointBytes5Writer.finish,List.map_append,map_bytes]

theorem erase_eq {H : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 H) (hash : H)
    (p : Prepared) (a : Accumulator) (proof pub : Slice U8)
    (size : a.weights.val.length = 64)
    (qb : ∀ j : Fin 22, (p.queries.val[j.val]'(by simpa [p.queries.property] using j.isLt)).val < 262144)
    (canonical : CheckpointBytesBlocks.CanonicalFields (CheckpointBytesBody.fields p a size qb))
    (variant : p.variant = .S2) (next : a.next.val = 10) :
    erase D hash (code p a proof pub) =
      erase D hash (CheckpointBytes5Writer.writer p a proof pub) := by
  have hm := fun hp hu => materialize p a hp hu size qb canonical variant next
  have hf := fun hp hu hc => finish p a hp hu hc size qb canonical variant next
  simp only [code,CheckpointBytes5Writer.writer,erase_bind,erase_read,erase_lift,
    erase_pure,hm,hf,bind_tc_ok]

def writer {H : Type} (D : VTop_Stages.aspis_core.digest.Digest32 H)
    (p : AspisR1Stage2.verifier.Prepared) (a : AspisR1Stage2.verifier.Accumulator)
    (proof pub : Slice U8) (hash : H) : Result (alloc.vec.Vec U8) := do
  let ck ← erase (VTop_Checkpoint.digest D) hash (code (toPrepared p) (toAccumulator a) proof pub)
  ok ⟨ck.val,ck.property⟩

theorem writer_eq {H : Type} (D : VTop_Stages.aspis_core.digest.Digest32 H)
    (p : AspisR1Stage2.verifier.Prepared) (a : AspisR1Stage2.verifier.Accumulator)
    (proof pub : Slice U8) (hash : H)
    (fields : Port5Q2_Prepared.PreparedFields p)
    (size : a.weights.val.length = 64)
    (canonical : CheckpointBytesBlocks.CanonicalFields (Port3_DecodeCoherence.inventory p a size fields.queries))
    (next : a.next.val = 10) :
    writer D p a proof pub hash = Port3_CheckpointInstall.writer D p a proof pub hash := by
  unfold writer Port3_CheckpointInstall.writer
  rw [erase_eq (VTop_Checkpoint.digest D) hash (toPrepared p) (toAccumulator a) proof pub
    (by simpa only [toAccumulator,mapVec,List.length_map] using size) fields.queries canonical]
  · change toVariant p.variant = _
    rw [fields.variant]
    rfl
  · exact next

#print axioms writer_eq
#print axioms materialize
#print axioms u8_decode
#print axioms map_bytes
#print axioms finish
#print axioms erase_eq
end AspisR1.WAdm_SourceWriter
end
