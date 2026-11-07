import NLW_WriterRoot1
import NLW_ByteIdentity
set_option autoImplicit false
noncomputable section
namespace NLW_WriterPair
open Aeneas Aeneas.Std AspisR1
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open OraclePortCompactDraft OraclePortCheckpointAbiC5
/-- Exact semantic commitment state; root1 uses original row2 payload63. -/
def rootState (proof : Slice U8) (offset : Nat) : State :=
 (SemanticRecordCodec.decodeState (slice (MultiproofConeCanonical.bytesOf proof.val) offset 32)).getD (fun _=>0)
def Roots (p : Prepared) (proof : Slice U8) : Prop :=
 p.roots 0=rootState proof 16 ∧ p.roots 1=rootState proof 63

theorem map_slice (bytes : List U8) (start count : Nat) :
 MultiproofConeCanonical.bytesOf ((bytes.drop start).take count)=
 slice (MultiproofConeCanonical.bytesOf bytes) start count := by
 simp only [MultiproofConeCanonical.bytesOf,slice,List.map_take,List.map_drop]
theorem encoded_state_bytes (s : State) :
 MultiproofConeCanonical.bytesOf (encodeState s).val=bytes s := by
 exact (CheckpointBytesDigest.bytes_stateOf (encodeState s)).symm.trans
  (congrArg bytes (state_roundtrip s))
/-- Serialized roots are proved from the source writer's actual encoding;
this consumes an OLD-writer Prepared/root provenance fact,not Root0 on the
new caller arguments. Native writer/argument installation remains separate. -/
theorem both (H : Bytes → State) (proof pub saved : Slice U8) (p : Prepared)
 (a : QueryAccumulator.State K E)
 (encoding : MultiproofConeCanonical.bytesOf saved.val=
  encode H (MultiproofConeCanonical.bytesOf proof.val) (MultiproofConeCanonical.bytesOf pub.val) p a)
 (roots : Roots p proof) : NLW_CommittedRoots.Both saved proof := by
 constructor
 · apply NLW_ByteIdentity.bytes_injective
   rw [map_slice,encoding,NLW_WriterRoot0.encoded]
   change bytes (p.roots 0)=MultiproofConeCanonical.bytesOf (encodeState (rootState proof 16)).val
   rw [encoded_state_bytes]
   exact congrArg bytes roots.1
 · apply NLW_ByteIdentity.bytes_injective
   rw [map_slice,encoding,NLW_WriterRoot1.encoded]
   change bytes (p.roots 1)=MultiproofConeCanonical.bytesOf (encodeState (rootState proof 63)).val
   rw [encoded_state_bytes]
   exact congrArg bytes roots.2
#print Roots
#print map_slice
#print encoded_state_bytes
#print both
#print axioms map_slice
#print axioms encoded_state_bytes
#print axioms both
end NLW_WriterPair
