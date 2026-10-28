import KNE_Composition
set_option autoImplicit false
noncomputable section
namespace AspisR1.KNE_Leaf
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open CheckpointBytes5Writer CheckpointBytes5Effect CheckpointBytes5Inputs
open CheckpointBytesDecodeC5 CheckpointBytesBody CheckpointBytesBlocks CheckpointBytesDigest
open MultiproofConeCanonical KNE_Model KNE_Schedule KNE_Caller KNE_Composition
open AspisR1Stage2.WireTx2 (singletonParts checksumParts)
attribute [local irreducible] sourceBody LPm_CheckpointBody.nativeBody

-- All115 body writes and the checksum write share the same physical relation.
-- Proof/public/checksum replies remain the three chronological oracle obligations.
theorem native_result {Hash : Type}
    (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (H : Bytes → State) (oracle : Oracle D hash H)
    (native : Bytes → Bytes → Bytes → Prop)
    (valid : LocalCorrect native KND_Schedule.schedule)
    (p : Prepared) (a : Accumulator) (domain : WriterDomain p a)
    (proof public1 : Slice U8) (hp hu hc : Digest) (body out : Slice U8) (before : Log)
    (tr : Trace native (bodyEmissions (fields p a domain.size domain.queriesBound)
      (stateOf hp) (stateOf hu)) [] (bytesOf body.val))
    (checksumWrite : native (bytesOf body.val) (bytesOf hc.val) (bytesOf out.val))
    (proofCall : D.digest hash (singletonParts proof) = ok hp)
    (publicCall : D.digest hash (singletonParts public1) = ok hu)
    (checksumCall : D.digest hash (checksumParts body) = ok hc) :
    out.val.length = 1768 ∧
    out = LPm_CheckpointProgram.returned p a domain.size domain.queriesBound
      domain.canonical domain.next hp hu hc ∧
    run D hash (writer p a proof public1) before =
      ok (out,((before ++ [(singletonParts proof,hp)]) ++
        [(singletonParts public1,hu)]) ++ [(checksumParts body,hc)]) ∧
    bytesOf out.val = OraclePortCheckpointAbiC5.encode H (bytesOf proof.val) (bytesOf public1.val)
      (CheckpointBytesBlocks.prepared (fields p a domain.size domain.queriesBound) domain.canonical)
      (CheckpointBytesBlocks.accumulator (fields p a domain.size domain.queriesBound) domain.canonical) := by
  have decoded := (body_bytes native valid p a domain hp hu hc body tr).trans
    (LPm_CheckpointBody.source_body p a domain.size domain.queriesBound
      domain.canonical domain.next hp hu)
  have bodyEq : body = bodySlice p a hp hu := by
    apply Subtype.ext
    apply MultiproofConeByteEquality.bytes_injective
    exact decoded.trans (bytes_roundtrip _).symm
  have bodyLen : (bytesOf body.val).length = 1736 := by
    rw [decoded]
    simp only [sourceBody,List.length_ofFn]
  have sumMem : (⟨"checksum",1736,1768,32⟩ : KND_Schedule.Step) ∈
      KND_Schedule.schedule := by decide
  have append := valid _ sumMem _ _ _ bodyLen
    (by simp only [bytesOf,List.length_map,hc.property]; rfl) checksumWrite
  have output : out.val = body.val ++ hc.val := by
    apply MultiproofConeByteEquality.bytes_injective
    simpa only [bytesOf,List.map_append] using append
  have outEq : out = finish p a hp hu hc := by
    apply Subtype.ext
    rw [output,bodyEq]
    rfl
  have outLen : out.val.length = 1768 := by
    rw [output,List.length_append]
    have h : body.val.length = 1736 := by
      simpa only [bytesOf,List.length_map] using bodyLen
    rw [h,hc.property]
    rfl
  have runEq : run D hash (writer p a proof public1) before =
      ok (out,((before ++ [(singletonParts proof,hp)]) ++
        [(singletonParts public1,hu)]) ++ [(checksumParts body,hc)]) := by
    rw [bodyEq] at checksumCall
    simp only [writer,run_bind,run_read,run_pure,proofCall,publicCall,checksumCall,
      bind_tc_ok,Aeneas.Std.uncurry]
    rw [outEq,bodyEq]
  refine ⟨outLen,?_,runEq,?_⟩
  · rw [LPm_CheckpointProgram.returned_eq]
    exact outEq
  · exact (writer_effects D hash H oracle p a proof public1 out domain.size
      domain.queriesBound domain.canonical domain.next before _ runEq).1

#print axioms native_result
end AspisR1.KNE_Leaf
end
