import Port11PROV_WriterReached
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port11PROV_WriterRoots
open Aeneas Aeneas.Std Result VTop_Stages
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open MultiproofConeCanonical OraclePortCompactDraft
open CheckpointBytes3Namespaces CheckpointBytesDecodeC5 CheckpointBytes5Effect

private theorem body_slice (p : CheckpointBytes5Writer.Prepared) (a : CheckpointBytes5Writer.Accumulator)
    (hp hu root : Digest) (offset : Nat) (fit : offset+32≤1736)
    (point : ∀ j : Fin 32, OraclePortCkptAbi2Extracted.body_byte p a hp hu
      (Usize.ofNat (offset+j.val) (by have := j.isLt; scalar_tac))=
      ok (root.val[j.val]'(by simpa only [root.property] using j.isLt))) :
    slice (sourceBody p a hp hu) offset 32=bytesOf root.val := by
  apply List.ext_getElem
  · simp only [slice,List.length_take,List.length_drop,sourceBody,List.length_ofFn,bytesOf,List.length_map,root.property]
    omega
  · intro j hj hk
    have bound : j<32 := by simpa only [bytesOf,List.length_map,root.property] using hk
    simp only [slice,List.getElem_take,List.getElem_drop,sourceBody,List.getElem_ofFn,bytesOf,List.getElem_map]
    exact congrArg (fun r => match r with | ok x => AspisV8R19.SqueezeOracleBridge.decodeByte x | _ => 0)
      (point ⟨j,bound⟩)

theorem root_slices (p : verifier.Prepared) (a : verifier.Accumulator) (hp hu : Digest) :
    slice (sourceBody (toPrepared p) (toAccumulator a) hp hu) 112 32=bytesOf (Port3_BatchStage.root0 p).val ∧
    slice (sourceBody (toPrepared p) (toAccumulator a) hp hu) 144 32=bytesOf (Port3_BatchStage.root1 p).val := by
  constructor
  · apply body_slice _ _ _ _ _ 112 (by decide)
    intro j
    exact CheckpointBytesSparseDigest.root0_dispatch _ _ hp hu (Usize.ofNat j.val (by scalar_tac)) j.isLt
  · apply body_slice _ _ _ _ _ 144 (by decide)
    intro j
    exact CheckpointBytesSparseDigest.root1_dispatch _ _ hp hu (Usize.ofNat j.val (by scalar_tac)) j.isLt

/-- Unconditional raw source root retention, requiring neither Prepared
canonicality nor a model BodyMatches witness. -/
theorem saved {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X)
    (p : verifier.Prepared) (a : verifier.Accumulator) (proof pub : Slice U8)
    (ck : alloc.vec.Vec U8) (success : Port3_CheckpointInstall.writer D p a proof pub hash=ok ck) :
    ck.val.length=1768 ∧
    slice (bytesOf ck.val) 112 32=bytesOf (Port3_BatchStage.root0 p).val ∧
    slice (bytesOf ck.val) 144 32=bytesOf (Port3_BatchStage.root1 p).val := by
  obtain ⟨after,ran⟩ := Port3_CheckpointInstall.writer_run D p a proof pub hash ck success []
  have erased := run_success _ _ _ _ _ _ ran
  simp only [CheckpointBytes5Writer.writer,erase_bind,erase_read,erase_pure] at erased
  obtain ⟨hp,hpCall,tail⟩ := OraclePortCkptAbiTry.bind_success _ _ _ erased
  obtain ⟨hu,huCall,tail⟩ := OraclePortCkptAbiTry.bind_success _ _ _ tail
  obtain ⟨hc,hcCall,tail⟩ := OraclePortCkptAbiTry.bind_success _ _ _ tail
  have ckEq := Result.ok.inj tail
  have content := congrArg (fun s : Slice U8 => bytesOf s.val) ckEq
  change bytesOf (CheckpointBytes5Writer.finish (toPrepared p) (toAccumulator a) hp hu hc).val=bytesOf ck.val at content
  rw [CheckpointBytes5Writer.finish_bytes] at content
  have length : ck.val.length=1768 := by
    have length := congrArg List.length content
    simp only [sourceBody,List.length_ofFn,List.length_append,bytes,bytesOf,List.length_map] at length
    omega
  have roots := root_slices p a hp hu
  have prefix : ∀ offset, offset+32≤1736 →
      slice (bytesOf ck.val) offset 32=slice (sourceBody (toPrepared p) (toAccumulator a) hp hu) offset 32 := by
    intro offset bound
    rw [← content]
    unfold slice
    rw [List.drop_append_of_le_length (by simpa only [sourceBody,List.length_ofFn] using (show offset≤1736 by omega))]
    rw [List.take_append_of_le_length (by simp only [sourceBody,List.length_drop,List.length_ofFn];omega)]
  exact ⟨length,(prefix 112 (by decide)).trans roots.1,(prefix 144 (by decide)).trans roots.2⟩

#print axioms body_slice
#print axioms root_slices
#print axioms saved
end AspisR1.Port11PROV_WriterRoots
end
