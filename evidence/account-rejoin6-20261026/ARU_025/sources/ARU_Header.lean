import CPhy_Header
import CPhy_HeaderCells
import SdkD_WriterRoots
import Tx2N_Header
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARU_Header
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open MultiproofConeCanonical OraclePortCompactDraft CheckpointBytesDigest

open CPhy_Header
theorem writer {Hash : Type} (D : VTop_Stages.aspis_core.digest.Digest32 Hash)
    (hash : Hash) (H : Bytes → State)
    (p : AspisR1Stage2.verifier.Prepared) (a : AspisR1Stage2.verifier.Accumulator)
    (proof pub : Slice U8) (saved : alloc.vec.Vec U8)
    (oracle : ∀ parts digest,
      (AspisV8R19.SqueezeOracleBridge.flatten parts = bytesOf proof.val ∨
       AspisV8R19.SqueezeOracleBridge.flatten parts = bytesOf pub.val) →
      (VTop_Checkpoint.digest D).digest hash parts = ok digest →
      CheckpointBytesDigest.stateOf digest = H (AspisV8R19.SqueezeOracleBridge.flatten parts))
    (success : Port3_CheckpointInstall.writer D p a proof pub hash = ok saved) :
    decode (bytesOf saved.val) = some (H (bytesOf proof.val),H (bytesOf pub.val)) ∧
    saved.val.length = 1768 := by
  unfold Port3_CheckpointInstall.writer at success
  obtain ⟨ck,hck,rest⟩ := OraclePortCkptAbiTry.bind_success _ _ _ success
  have source := congrArg (fun v : alloc.vec.Vec U8 => v.val) (Result.ok.inj rest)
  simp only [CheckpointBytes5Writer.writer,CheckpointBytes5Effect.erase_bind,
    CheckpointBytes5Effect.erase_read,CheckpointBytes5Effect.erase_pure] at hck
  obtain ⟨hp,hpCall,tail⟩ := OraclePortCkptAbiTry.bind_success _ _ _ hck
  obtain ⟨hu,huCall,tail⟩ := OraclePortCkptAbiTry.bind_success _ _ _ tail
  obtain ⟨hc,hcCall,tail⟩ := OraclePortCkptAbiTry.bind_success _ _ _ tail
  have same := Result.ok.inj tail
  subst ck
  have encoded := congrArg bytesOf source.symm
  rw [CheckpointBytes5Writer.finish_bytes] at encoded
  have size : saved.val.length = 1768 := by
    rw [← source]
    simp only [CheckpointBytes5Writer.finish,List.length_append,List.length_map,
      CheckpointBytesDecodeC5.sourceBody,List.length_ofFn,hc.property]
    rfl
  have hpEq := oracle _ _ (Or.inl (CheckpointBytes5Inputs.singleton_input proof)) hpCall
  have huEq := oracle _ _ (Or.inr (CheckpointBytes5Inputs.singleton_input pub)) huCall
  rw [CheckpointBytes5Inputs.singleton_input] at hpEq huEq
  refine ⟨decode_fields _ _ _ (by simp only [bytesOf,List.length_map,size]; decide) ?_ ?_,size⟩
  · rw [encoded,SdkD_WriterRoots.slice_append _ _ 16 32 (by
      simp only [CheckpointBytesDecodeC5.sourceBody,List.length_ofFn]; decide),
      CPhy_HeaderCells.proofHash,← bytes_stateOf,hpEq]
  · rw [encoded,SdkD_WriterRoots.slice_append _ _ 48 32 (by
      simp only [CheckpointBytesDecodeC5.sourceBody,List.length_ofFn]; decide),
      CPhy_HeaderCells.publicHash,← bytes_stateOf,huEq]

theorem reader (reserved : Bool) {Hash : Type}
    (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash) (H : Bytes → State)
    (checkpoint proof pub : Slice U8) (p : AspisR1Stage2.verifier.Prepared)
    (a : AspisR1Stage2.verifier.Accumulator)
    (oracle : ∀ parts digest,
      (AspisV8R19.SqueezeOracleBridge.flatten parts = bytesOf proof.val ∨
       AspisV8R19.SqueezeOracleBridge.flatten parts = bytesOf pub.val) →
      D.digest hash parts = ok digest →
      CheckpointBytesDigest.stateOf digest = H (AspisV8R19.SqueezeOracleBridge.flatten parts))
    (success : AspisR1Stage2.verifier.resumeWithOps (CheckpointBytes4Ops.ops reserved)
      D checkpoint proof pub .S2 hash = ok (.Ok (p,a))) :
    decode (bytesOf checkpoint.val) = some (H (bytesOf proof.val),H (bytesOf pub.val)) := by
  obtain ⟨c⟩ := CheckpointBytes4Comparison.successful_calls reserved D checkpoint proof pub .S2 hash p a success
  obtain ⟨_,_,_,_,_,length,_⟩ := Tx2N_Header.cuts reserved D checkpoint proof pub hash p a success
  have proofRead := MultiproofConeSlices.range_total checkpoint 16#usize 48#usize (by decide)
    (by change 48 ≤ checkpoint.val.length; omega)
  have pubRead := MultiproofConeSlices.range_total checkpoint 48#usize 80#usize (by decide)
    (by change 80 ≤ checkpoint.val.length; omega)
  have proofEq := congrArg Subtype.val (Result.ok.inj (proofRead.symm.trans c.proofField))
  have pubEq := congrArg Subtype.val (Result.ok.inj (pubRead.symm.trans c.publicField))
  have inputs := CheckpointBytes5Inputs.calls_inputs D hash checkpoint proof pub c length
  have hpEq := oracle _ _ (Or.inl inputs.1) c.proofCall
  have huEq := oracle _ _ (Or.inr inputs.2.1) c.publicCall
  rw [inputs.1] at hpEq
  rw [inputs.2.1] at huEq
  apply decode_fields _ _ _ (by simp only [bytesOf,List.length_map,length]; decide)
  · rw [← hpEq,bytes_stateOf,← c.proofEqual,← proofEq]
    exact (MultiproofConeSlices.bytes_sub checkpoint 16#usize 48#usize).symm
  · rw [← huEq,bytes_stateOf,← c.publicEqual,← pubEq]
    exact (MultiproofConeSlices.bytes_sub checkpoint 48#usize 80#usize).symm

#print axioms writer
#print axioms reader
end AspisR1.ARU_Header
end
