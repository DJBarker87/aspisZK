import NKA_ClaimsEffects
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKA_ClaimsOwnership
open Aeneas Aeneas.Std Result

def Bound (reservation : NP6_StdModel.Reservation) (rows : NKA_HeapCarrier.RowNative)
 (box : NKA_HeapCarrier.BoxNative) (owner : Nat) (before : NKA_InitializedPrefix.Memory)
 (value : AspisR1ClaimsUnrolledParent.Claims) : Prop :=
 match reservation with
 | .Err _ => True
 | .Ok _ => let storage:=NKA_InitHistory.completed (NKA_InitializedPrefix.run (NKA_HeapCarrier.memoryNative rows)
    (NKA_HeapCarrier.rows (NKA_ClaimsEffects.main value)) before)
   let post:=box owner storage
   NKA_InitHistory.Ready storage ∧ post.owner=owner ∧ post.length=1

theorem bound (reservation : NP6_StdModel.Reservation) (rows : NKA_HeapCarrier.RowNative)
 (rowCut : NKA_HeapCarrier.RowCut rows) (box : NKA_HeapCarrier.BoxNative)
 (boxCut : NKA_HeapCarrier.BoxCut box) (owner : Nat) (before : NKA_InitializedPrefix.Memory)
 (value : AspisR1ClaimsUnrolledParent.Claims) : Bound reservation rows box owner before value := by
 cases reservation with
 | Err _ => trivial
 | Ok _ => exact ⟨NKA_InitHistory.ready _,
   NKA_HeapCarrier.ownership rows rowCut box boxCut owner before (NKA_ClaimsEffects.main value)⟩

/-- An aborting allocator action enters no owned-storage continuation. This
is a conclusion case split, never a successful-allocation premise. -/
def AtAllocation {A : Type} (allocation : Result A) (reservation : NP6_StdModel.Reservation)
 (rows : NKA_HeapCarrier.RowNative) (box : NKA_HeapCarrier.BoxNative) (owner : Nat)
 (before : NKA_InitializedPrefix.Memory) (value : AspisR1ClaimsUnrolledParent.Claims) : Prop :=
 match allocation with
 | .ok _ => Bound reservation rows box owner before value
 | _ => True

theorem at_allocation {A : Type} (allocation : Result A) (reservation : NP6_StdModel.Reservation)
 (rows : NKA_HeapCarrier.RowNative) (rowCut : NKA_HeapCarrier.RowCut rows)
 (box : NKA_HeapCarrier.BoxNative) (boxCut : NKA_HeapCarrier.BoxCut box) (owner : Nat)
 (before : NKA_InitializedPrefix.Memory) (value : AspisR1ClaimsUnrolledParent.Claims) :
 AtAllocation allocation reservation rows box owner before value := by
 cases allocation with
 | fail _ => trivial
 | div => trivial
 | ok _ => exact bound reservation rows rowCut box boxCut owner before value

#print axioms at_allocation
#print axioms bound
end AspisR1.NKA_ClaimsOwnership
end
