import NNC_WriterCells
import NLW_ReaderHeader
set_option autoImplicit false
noncomputable section
namespace NNC_WriterHeader
open Aeneas Aeneas.Std Result AspisR1
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open CheckpointBytes5Effect CheckpointBytesDigest MultiproofConeCanonical
/-- Header matching from the SAME actual writer call. No reader, state
canonicality, ten-step model equation, or TX2 acceptance is required. -/
theorem returned {X : Type} (D : VTop_Stages.aspis_core.digest.Digest32 X)
 (p : AspisR1Stage2.verifier.Prepared) (a : AspisR1Stage2.verifier.Accumulator)
 (proof pub : Slice U8) (hash : X) (saved : alloc.vec.Vec U8)
 (H : Bytes → State)
 (oracle : CheckpointBytes5Inputs.Oracle (VTop_Checkpoint.digest D) hash H)
 (success : Port3_CheckpointInstall.writer D p a proof pub hash=ok saved) :
 NLW_ReaderHeader.decode (bytesOf saved.val)=some (H (bytesOf proof.val),H (bytesOf pub.val)) := by
 unfold Port3_CheckpointInstall.writer at success
 obtain ⟨ck,hck,rest⟩ := OraclePortCkptAbiTry.bind_success _ _ _ success
 have savedBytes := congrArg (fun v : alloc.vec.Vec U8 => v.val) (Result.ok.inj rest)
 simp only [CheckpointBytes5Writer.writer,erase_bind,erase_read,erase_pure] at hck
 obtain ⟨hp,hpCall,tail⟩ := OraclePortCkptAbiTry.bind_success _ _ _ hck
 obtain ⟨hu,huCall,tail⟩ := OraclePortCkptAbiTry.bind_success _ _ _ tail
 obtain ⟨hc,_,tail⟩ := OraclePortCkptAbiTry.bind_success _ _ _ tail
 have same := Result.ok.inj tail
 subst ck
 have encoded := congrArg bytesOf savedBytes.symm
 rw [CheckpointBytes5Writer.finish_bytes] at encoded
 have hpEq := oracle _ _ hpCall
 have huEq := oracle _ _ huCall
 rw [CheckpointBytes5Inputs.singleton_input] at hpEq huEq
 have bodyLength : (CheckpointBytesDecodeC5.sourceBody (CheckpointBytes3Namespaces.toPrepared p)
  (CheckpointBytes3Namespaces.toAccumulator a) hp hu).length=1736 := by
  simp only [CheckpointBytesDecodeC5.sourceBody,List.length_ofFn]
 unfold NLW_ReaderHeader.decode
 rw [encoded,SdkD_WriterRoots.slice_append _ _ 16 32 (by rw [bodyLength];omega),
  SdkD_WriterRoots.slice_append _ _ 48 32 (by rw [bodyLength];omega),
  NNC_WriterCells.proofHash,NNC_WriterCells.publicHash,
  ←bytes_stateOf,←bytes_stateOf,SemanticRecordCodec.decodeState_bytes,
  SemanticRecordCodec.decodeState_bytes]
 simp only [Option.bind_some,hpEq,huEq]
 rfl
#print axioms returned
end NNC_WriterHeader
