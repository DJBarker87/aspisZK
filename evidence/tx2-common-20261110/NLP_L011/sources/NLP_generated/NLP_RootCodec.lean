import NLP_RootDomain
set_option autoImplicit false
noncomputable section
namespace NLP_RootCodec
open Aeneas Aeneas.Std Result AspisR1
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
/-- Fixed digest carrier roundtrip, symbolic in every byte. -/
theorem decode_array (root : Array U8 32#usize) :
 encodeState ((SemanticRecordCodec.decodeState (MultiproofConeCanonical.bytesOf root.val)).getD (fun _=>0))=root := by
 rw [←MultiproofConePhysicalTransport.digest_bytes root,SemanticRecordCodec.decodeState_bytes]
 exact array_roundtrip root
/-- Parsed is an interpretation witness; the wire is fixed and semantic root1
is selected from the SAME actual input root. This asserts no parser success. -/
def parsed (proof : Slice U8) (root1 : Array U8 32#usize) : OraclePortCompactDraft.Parsed :=
 ⟨MultiproofConeCanonical.bytesOf proof.val,
 [[],[],List.replicate 5 0++MultiproofConeCanonical.bytesOf root1.val]⟩
theorem wire (proof : Slice U8) (root1 : Array U8 32#usize) :
 (parsed proof root1).wire=MultiproofConeCanonical.bytesOf proof.val := rfl
theorem kind1 (proof : Slice U8) (root1 : Array U8 32#usize) :
 encodeState (OraclePortBatchDraft.committedRoot (parsed proof root1) 1)=root1 := by
 change encodeState ((SemanticRecordCodec.decodeState
  ((List.replicate 5 0++MultiproofConeCanonical.bytesOf root1.val).drop 5)).getD (fun _=>0))=root1
 have drop : (List.replicate 5 (0 : Byte)++MultiproofConeCanonical.bytesOf root1.val).drop 5=
  MultiproofConeCanonical.bytesOf root1.val := by simp
 rw [drop]
 exact decode_array root1
#print parsed
#print decode_array
#print wire
#print kind1
#print axioms decode_array
#print axioms wire
#print axioms kind1
end NLP_RootCodec
