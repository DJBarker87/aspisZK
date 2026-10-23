import S2SdkProofGateJoinV1
import S2CheckpointGuardTransportV1
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisS2OwnedStage1.SdkReference.FirstEntryNormalization

/-- Byte initialization used only by the paired native/reference fixture.
These are lists of the actual input bytes, not a replacement SDK carrier. -/
def proofImage (proof : Slice U8) (candidate : Array U8 688#usize) : List U8 :=
  (candidate.val ++ proof.val.drop 688).set 696 2#u8

/-- The existing exact source comparator removes the fixture's seeded prefix
premise. The native constructor cut supplies the tag and scan observations;
actual source interpretation of those cuts remains a separate obligation. -/
theorem proof_image_identity (proof : Slice U8) (candidate : Array U8 688#usize)
    (same : ProofPrefixParent.stdCmp
      (ProofGate.takePrefix proof (Array.to_slice candidate)) candidate=ok false)
    (tag : proof.val[696]?=some 2#u8) :
    proofImage proof candidate=proof.val := by
  have comparison :
      core.slice.cmp.PartialEqSlice.ne core.cmp.PartialEqU8
        (ProofGate.takePrefix proof (Array.to_slice candidate)) (Array.to_slice candidate)=ok false := same
  rw [ProofGate.standard_ne] at comparison
  have hpref : (ProofGate.takePrefix proof (Array.to_slice candidate)).val=
      (Array.to_slice candidate).val := by
    have h := Result.ok.inj comparison
    simpa using h
  have n : candidate.val.length=688 := candidate.property
  have take : proof.val.take 688=candidate.val := by
    simpa [ProofGate.takePrefix,Array.to_slice,n] using hpref
  have index : 696<proof.val.length := by
    by_contra outside
    rw [List.getElem?_eq_none (by omega)] at tag
    cases tag
  have byte : proof.val[696]=2#u8 := by
    rw [List.getElem?_eq_getElem index] at tag
    exact Option.some.inj tag
  unfold proofImage
  rw [←take,List.take_append_drop,←byte,List.set_getElem_self index]

/-- Existing total scanner semantics remove the all-zero initialization
premise, without normalizing 1768 concrete entries in the kernel. -/
theorem checkpoint_image_identity (checkpoint : alloc.vec.Vec U8)
    (size : checkpoint.val.length=1768)
    (scanned : CheckpointGuardTransport.stdAny checkpoint.val=false) :
    List.replicate 1768 (0#u8)=checkpoint.val := by
  symm
  apply List.eq_replicate_iff.mpr
  exact ⟨size,(CheckpointGuardTransport.stdAny_false checkpoint.val).mp scanned⟩

/-- Equality transport for an arbitrary complete caller/heap/result context.
No assertion that the real native source already has these observations, or
that it equals the borrowed reference, is hidden in this local theorem. -/
theorem context_transport {A : Type} (proof : Slice U8)
    (candidate : Array U8 688#usize) (checkpoint : alloc.vec.Vec U8)
    (same : ProofPrefixParent.stdCmp
      (ProofGate.takePrefix proof (Array.to_slice candidate)) candidate=ok false)
    (tag : proof.val[696]?=some 2#u8)
    (size : checkpoint.val.length=1768)
    (scanned : CheckpointGuardTransport.stdAny checkpoint.val=false)
    (context : List U8 → List U8 → Result A) :
    context (proofImage proof candidate) (List.replicate 1768 (0#u8))=
      context proof.val checkpoint.val := by
  rw [proof_image_identity proof candidate same tag,
    checkpoint_image_identity checkpoint size scanned]

#print axioms proof_image_identity
#print axioms checkpoint_image_identity
#print axioms context_transport
end AspisS2OwnedStage1.SdkReference.FirstEntryNormalization
