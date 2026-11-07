import NMC_HeapLaws
import NLU_ClaimsInstall
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMC_Claims
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NMC_Parent
abbrev Status := NKA_HeapCarrier.Status
structure Returned (A : Type) where
 status : Status
 allocator : A
 heap : Heap
 owned : Option OwnedClaims
/-- A full child Result is attached to the ONE parent heap. Successful data
comes from that Result, never from the numeric identity. An outer abort has
no after-state. Allocation is inside the child packet, not repeated here. -/
def attach {A : Type} (heap : Heap) (identity : Nat)
 (child : Result (Status×A)) : Result (Returned A) := do
 let (status,allocator) ← child
 match status with
 | .Err error=>ok ⟨.Err error,allocator,heap,none⟩
 | .Ok claims=>ok ⟨.Ok claims,allocator,write heap identity (some claims),some ⟨identity,claims⟩⟩
/-- The complete native/reference/cohort child packets are installed at the
same original prefix, same Reservation and same allocator state. No
successful child or independently chosen decoded value is a premise. -/
theorem installed {A H : Type} (input : NLU.Input H) (domain : NLU.InputDomain input)
 (allocator : S2W_D189Wrappers.Allocator A) (state : A)
 (rows : NKA_HeapCarrier.RowNative) (rowCut : NKA_HeapCarrier.RowCut rows)
 (box : NKA_HeapCarrier.BoxNative) (boxCut : NKA_HeapCarrier.BoxCut box)
 (identity : Nat) (before : NKA_InitializedPrefix.Memory) (heap : Heap) :
 ∃ value,
 NKA_ClaimsOwnership.AtAllocation (NKA_ClaimsEffects.allocate allocator state) input.reservation rows box identity before value ∧
 attach heap identity (NKA_ClaimsEffects.native allocator state input.reservation rows box identity before value)=
 attach heap identity (NKA_ClaimsEffects.cohort allocator state input.reservation input.prefix1) ∧
 attach heap identity (NKA_ClaimsEffects.native allocator state input.reservation rows box identity before value)=
 attach heap identity (NKA_ClaimsEffects.reference allocator state input.reservation input.prefix1) := by
 obtain ⟨value,allocated,native,reference,_⟩:=NLU_Claims.source input domain allocator state rows rowCut box boxCut identity before
 exact ⟨value,allocated,congrArg (attach heap identity) native,congrArg (attach heap identity) reference⟩
/-- The disjoint rest heap is retained on every returning arm, including Err. -/
theorem frame {A : Type} (heap : Heap) (identity address : Nat)
 (child : Result (Status×A)) (after : Returned A)
 (returned : attach heap identity child=ok after) (disjoint : address≠identity) :
 after.heap address=heap address := by
 cases child with
 | fail error=>cases returned
 | div=>cases returned
 | ok pair=>
   cases pair with
   | mk status allocator=>
     cases status with
     | Err error=>
       change ok (⟨.Err error,allocator,heap,none⟩ : Returned A)=ok after at returned
       cases Result.ok.inj returned
       rfl
     | Ok claims=>
       change ok (⟨.Ok claims,allocator,write heap identity (some claims),some ⟨identity,claims⟩⟩ : Returned A)=ok after at returned
       cases Result.ok.inj returned
       exact write_frame heap identity address (some claims) disjoint
/-- Child aborts do not acquire a claims owner or fabricate a new heap. -/
theorem abort {A : Type} (heap : Heap) (identity : Nat) (error : Error) :
 attach (A:=A) heap identity (fail error)=fail error := rfl
#print axioms installed
#print axioms frame
#print axioms abort
set_option pp.proofs false in #print installed
end AspisR1.NMC_Claims
end
