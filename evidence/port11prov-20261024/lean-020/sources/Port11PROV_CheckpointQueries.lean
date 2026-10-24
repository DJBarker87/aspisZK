import Port11PROV_CheckpointRoots
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port11PROV_CheckpointQueries
open Aeneas Aeneas.Std Result VTop_Stages
open MultiproofConeCanonical OraclePortCompactDraft
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open CheckpointBytes3Namespaces CheckpointBytesDecodeC5 CheckpointBytes5Effect

theorem query_slice (p : CheckpointBytes5Writer.Prepared) (a : CheckpointBytes5Writer.Accumulator)
    (hp hu : Digest) (j : Fin 22) :
    slice (sourceBody p a hp hu) (320+j.val*4) 4=
      le32 (p.queries.val[j.val]'(by simpa [p.queries.property] using j.isLt)).val := by
  apply List.ext_getElem
  · simp only [slice,List.length_take,List.length_drop,sourceBody,List.length_ofFn]
    have bound := j.isLt
    simp only [le32,List.length_map,List.length_range]
    omega
  · intro i hi hk
    have ib : i<4 := by simpa only [le32,List.length_map,List.length_range] using hk
    obtain ⟨v,run,value⟩ := CheckpointBytesQuery.query_bytes p a hp hu j (Usize.ofNat i (by scalar_tac)) ib
    have address : 320+j.val*4+i=320+4*j.val+i := by omega
    have same := Option.some.inj ((List.getElem?_eq_getElem hk).symm.trans value)
    simp only [slice,List.getElem_take,List.getElem_drop,sourceBody,List.getElem_ofFn,address,run]
    exact same.symm

theorem saved {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X)
    (p : verifier.Prepared) (a : verifier.Accumulator) (proof pub : Slice U8)
    (ck : alloc.vec.Vec U8) (success : Port3_CheckpointInstall.writer D p a proof pub hash=ok ck)
    (j : Fin 22) : slice (bytesOf ck.val) (320+j.val*4) 4=
      le32 (p.queries.val[j.val]'(by simpa [p.queries.property] using j.isLt)).val := by
  obtain ⟨after,ran⟩ := Port3_CheckpointInstall.writer_run D p a proof pub hash ck success []
  have erased := run_success _ _ _ _ _ _ ran
  simp only [CheckpointBytes5Writer.writer,erase_bind,erase_read,erase_pure] at erased
  obtain ⟨hp,hpCall,tail⟩ := OraclePortCkptAbiTry.bind_success _ _ _ erased
  obtain ⟨hu,huCall,tail⟩ := OraclePortCkptAbiTry.bind_success _ _ _ tail
  obtain ⟨hc,hcCall,tail⟩ := OraclePortCkptAbiTry.bind_success _ _ _ tail
  have content := congrArg (fun s : Slice U8 => bytesOf s.val) (Result.ok.inj tail)
  change bytesOf (CheckpointBytes5Writer.finish (toPrepared p) (toAccumulator a) hp hu hc).val=bytesOf ck.val at content
  rw [CheckpointBytes5Writer.finish_bytes] at content
  rw [← content]
  unfold slice
  rw [List.drop_append_of_le_length (by simp only [sourceBody,List.length_ofFn];have := j.isLt;omega)]
  rw [List.take_append_of_le_length (by simp only [sourceBody,List.length_drop,List.length_ofFn];have := j.isLt;omega)]
  exact query_slice (toPrepared p) (toAccumulator a) hp hu j

/-- Exact raw 22-word array retention across actual writer/current18 success;
no canonical/model query equality is supplied. -/
theorem accepted (reserved : Bool) (unwrap : Port6CK_Semantic.Unwrap)
    (unwrap_ok : ∀ N b, unwrap N (.Ok b)=ok b)
    {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X)
    (p0 p1 : verifier.Prepared) (written a1 : verifier.Accumulator)
    (proof pub : Slice U8) (ck : alloc.vec.Vec U8)
    (wrote : Port3_CheckpointInstall.writer D p0 written proof pub hash=ok ck)
    (resumed : Port6CK_Reader.reader reserved unwrap D ck.deref proof pub .S2 hash=ok (.Ok (p1,a1))) :
    p1.queries=p0.queries := by
  have len := (Port11PROV_WriterRoots.saved D hash p0 written proof pub ck wrote).1
  have retained := Port6CK_Reader.accepted reserved unwrap unwrap_ok D hash ck.deref proof pub p1 a1 resumed
  rw [Port4A_ReaderInstall.reference_eq] at retained
  have native := Port3_CheckpointInstall.reader_success reserved D ck.deref proof pub .S2 hash p1 a1 retained
  obtain ⟨f⟩ := OraclePortCkptAbiSourceFields.successful_fields _ _ ck.deref proof pub .S2 hash p1 a1 native
  have flat := CheckpointBytes4Layout.flat_fields reserved ck.deref p1 a1 f len
  have length0 : p0.queries.val.length=22 := p0.queries.property
  have length1 : p1.queries.val.length=22 := p1.queries.property
  have reads := CheckpointBytes4QueryDecode.query_values reserved f.rRho f.rQueries p1.queries.val f.queriesRead
    (by rw [flat.rhoCursor,flat.rhoBacking,length1];change 320+22*4≤ck.val.length;omega)
  apply Subtype.ext
  apply List.ext_getElem
  · omega
  · intro j hj hk
    have bound : j<22 := by omega
    have value := reads ⟨j,hj⟩
    rw [flat.rhoCursor,flat.rhoBacking] at value
    change little (slice (bytesOf ck.val) (320+j*4) 4)=_ at value
    rw [saved D hash p0 written proof pub ck wrote ⟨j,bound⟩] at value
    rw [OraclePortCheckpointPreparedC5.little_le32 _ (by scalar_tac)] at value
    exact UScalar.eq_of_val_eq value.symm

#print axioms query_slice
#print axioms saved
#print axioms accepted
end AspisR1.Port11PROV_CheckpointQueries
end
