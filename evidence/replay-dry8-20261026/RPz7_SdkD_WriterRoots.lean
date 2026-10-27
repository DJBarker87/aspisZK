import RPz7_SdkD_WriterRoot1
import RPz7_SdkD_WriterSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.SdkD_WriterRoots
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open MultiproofConeCanonical OraclePortCompactDraft

theorem slice_append (left right : Bytes) (offset size : Nat) (room : offset+size ≤ left.length) :
    slice (left++right) offset size = slice left offset size := by
  have first : (left++right).take left.length = left := by simp
  have same := SdkD_SliceAlgebra.take_drop_take (left++right) offset size left.length room
  rw [first] at same
  exact same.symm

theorem returned {Hash : Type} (D : VTop_Stages.aspis_core.digest.Digest32 Hash)
    (p : AspisR1Stage2.verifier.Prepared) (a : AspisR1Stage2.verifier.Accumulator)
    (proof pub : Slice U8) (hash : Hash) (saved : alloc.vec.Vec U8)
    (success : Port3_CheckpointInstall.writer D p a proof pub hash = ok saved) :
    slice (bytesOf saved.val) 112 32 = bytesOf (Port3_BatchStage.root0 p).val ∧
    slice (bytesOf saved.val) 144 32 = bytesOf (Port3_BatchStage.root1 p).val := by
  obtain ⟨hp,hu,hc,source⟩ := SdkD_WriterSource.returned D p a proof pub hash saved success
  have encoded := congrArg bytesOf source
  rw [CheckpointBytes5Writer.finish_bytes] at encoded
  rw [encoded]
  have bodyLength : (CheckpointBytesDecodeC5.sourceBody (CheckpointBytes3Namespaces.toPrepared p)
      (CheckpointBytes3Namespaces.toAccumulator a) hp hu).length = 1736 := by
    simp only [CheckpointBytesDecodeC5.sourceBody,List.length_ofFn]
  rw [slice_append _ _ 112 32 (by rw [bodyLength]; decide),
    slice_append _ _ 144 32 (by rw [bodyLength]; decide),
    SdkD_WriterCells.root0,SdkD_WriterRoot1.root1]
  have bound0 : 0 < p.roots.val.length := by simp [p.roots.property]
  have bound1 : 1 < p.roots.val.length := by simp [p.roots.property]
  simp only [Port3_BatchStage.root0,Port3_BatchStage.root1,
    List.getElem?_eq_getElem bound0,List.getElem?_eq_getElem bound1,Option.getD_some]
  exact ⟨rfl,rfl⟩

#print axioms slice_append
#print axioms returned
end AspisR1.SdkD_WriterRoots
end
