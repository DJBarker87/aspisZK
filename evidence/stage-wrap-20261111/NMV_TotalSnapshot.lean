import NMV_Model
set_option autoImplicit false
namespace NMV_TotalSnapshot
open NMV_Model NMV_Snapshot NLF_SdkModel

/-- Fail and divergence are distinct; no stopped constructor contains a world. -/
inductive Stop where
 | failed (reason : Aeneas.Std.Error)
 | diverged
 | allocation
 | copyAbort
inductive Outcome (α : Type) where
 | returned (world : World) (value : α)
 | stopped (reason : Stop) (trace : List RuntimeEvent)

/-- The allocation reply belongs to the existing std/allocator operation, not
the caller's domain. A failed allocation aborts before the shared guard drops. -/
def copying (w : World) (account l₁ l₂ : Nat) : Bool :=
 match (NLF_Bracket.snapshot w.sdk.state account w.sdk.next).2 with
 | .error _ => false
 | .ok payload => decide (payload.bytes.length=l₁ ∨ payload.bytes.length=l₂)

def run (w : World) (account l₁ l₂ : Nat) (allocationReturns : Bool) : Outcome Owned :=
 if copying w account l₁ l₂ && !allocationReturns then
   .stopped .allocation (w.runtime ++
     ((NLF_SnapshotEvents.events w.sdk.state account w.sdk.next).take 2).map RuntimeEvent.sdk)
 else
   .returned ⟨(NMV_Snapshot.run w.sdk account l₁ l₂).1,w.runtime ++
     (NLF_SnapshotEvents.events w.sdk.state account w.sdk.next).map RuntimeEvent.sdk⟩
      (NMV_Snapshot.run w.sdk account l₁ l₂).2

theorem allocation_success (w : World) (account l₁ l₂ : Nat) :
 run w account l₁ l₂ true =
   .returned ⟨(NMV_Snapshot.run w.sdk account l₁ l₂).1,w.runtime ++
     (NLF_SnapshotEvents.events w.sdk.state account w.sdk.next).map RuntimeEvent.sdk⟩
     (NMV_Snapshot.run w.sdk account l₁ l₂).2 := by simp [run]

theorem returned_frame (w after : World) (account l₁ l₂ : Nat) (alloc : Bool) (value : Owned)
 (h : run w account l₁ l₂ alloc = .returned after value) :
 after.sdk.state=w.sdk.state := by
 by_cases bad : (copying w account l₁ l₂ && !alloc)=true
 · simp only [run,if_pos bad] at h
   cases h
 · simp only [run,if_neg bad] at h
   cases h
   exact NMV_Snapshot.frame w.sdk account l₁ l₂

theorem allocation_abort (w : World) (account l₁ l₂ : Nat) (payload : Payload)
 (borrow : (NLF_Bracket.snapshot w.sdk.state account w.sdk.next).2 = .ok payload)
 (size : payload.bytes.length=l₁ ∨ payload.bytes.length=l₂) :
 run w account l₁ l₂ false =
  .stopped .allocation (w.runtime ++
   ((NLF_SnapshotEvents.events w.sdk.state account w.sdk.next).take 2).map RuntimeEvent.sdk) := by
 simp [run,copying,borrow,size]

/-- Deferred invalid-length and borrow-error arms perform no allocation, so
allocator failure cannot add an abort that the frozen function does not have. -/
theorem no_allocation (w : World) (account l₁ l₂ : Nat)
 (notCopying : match (NLF_Bracket.snapshot w.sdk.state account w.sdk.next).2 with
  | .error _ => True
  | .ok p => ¬ (p.bytes.length=l₁ ∨ p.bytes.length=l₂)) :
 run w account l₁ l₂ false = run w account l₁ l₂ true := by
 unfold run copying
 cases h : (NLF_Bracket.snapshot w.sdk.state account w.sdk.next).2 with
 | error e => simp [h]
 | ok p => simp only [h] at notCopying; simp [h,notCopying]

#print axioms allocation_success
#print axioms returned_frame
#print axioms allocation_abort
#print axioms no_allocation
end NMV_TotalSnapshot
