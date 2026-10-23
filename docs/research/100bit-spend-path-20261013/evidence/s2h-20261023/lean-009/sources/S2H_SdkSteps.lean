import S2H_HeapUpdate
import S2SdkOwnedBorrowTotalV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result AspisS2OwnedStage1
namespace AspisR1.S2H
open S2Trust S2E S2E_Reference.S2E_Reference

/-- Literal equality to the already checked symbolic owned primitive. -/
theorem shared_reference_port (sdk : SDK) (slot : Usize) :
    owned_acquire_shared sdk slot = SdkReference.owned_acquire_shared sdk slot := rfl

def sharedHeap {F : Type} (h : Heap F) (cell token owner : Nat)
    (reply : core.result.Result Unit PE) : Heap F :=
  match reply with
  | .Ok _ => acquire h cell token owner .shared
  | .Err _ => h

def sharedReply (token : Nat) (reply : core.result.Result Unit PE) : Reply :=
  match reply with
  | .Ok _ => .guard token
  | .Err _ => .borrowFailed

/-- Full-sized shared borrow primitive port, for BOTH success and rejection.
The actual source site still owes Enabled, runtime Library interpretation and
initial HeapImage. No native child, allocator or oracle callback is replaced.
Validity of the successor and a whole caller port are deliberately not claimed. -/
theorem shared_sdk_step {W Child Alloc Event : Type}
    (L : Library W (World Child Alloc Event)) (trust : S2TrustedSdkBorrow L)
    (m : AllocationMap) (n : W) (h : Heap (World Child Alloc Event)) (sdk : SDK)
    (related : L.related n h) (valid : Valid h) (image : HeapImage m h sdk)
    (index token owner : Nat) (account : OwnedAccount)
    (readAccount : sdk.accounts.val[index]? = some account)
    (enabled : Enabled h (.shared (m.handle index) token owner))
    (isize64 : (core.num.Isize.MAX : Isize).val = maxCounter) :
    ∃ (reply : core.result.Result Unit PE) (out : SDK) (after : W),
      owned_acquire_shared sdk account.data_slot = ok (reply,out) ∧
      L.run n (.shared (m.handle index) token owner) = (after,sharedReply token reply) ∧
      L.related after (sharedHeap h (m.dataCell account.data_slot.val) token owner reply) ∧
      HeapImage m (sharedHeap h (m.dataCell account.data_slot.val) token owner reply) out := by
  have bounds := (image.slots index account readAccount).1
  obtain ⟨cell,reply,out,actual,ran,alternatives⟩ :=
    SdkReference.BorrowTotal.shared_acquire_total sdk account.data_slot bounds
  have read : sdk.data_cells.val[account.data_slot.val]? = some cell := by
    exact List.getElem?_eq_some_iff.mpr ⟨bounds,actual.symm⟩
  have counter := (image.data account.data_slot.val cell read).2.2.2.1
  have handle := congrArg Prod.fst (image.handles index account readAccount)
  rw [← shared_reference_port] at ran
  rcases alternatives with failed | success
  · rcases failed with ⟨rfl,rfl,disallowed⟩
    have no : ¬ (0 ≤ h.counter (h.accounts (m.handle index)).1 ∧
        h.counter (h.accounts (m.handle index)).1 < maxCounter) := by
      rw [handle,counter]
      intro allowed
      apply disallowed
      constructor
      · change (0#isize).val ≤ cell.borrowed.val
        exact allowed.1
      · change cell.borrowed.val < (core.num.Isize.MAX : Isize).val
        rw [isize64]
        exact allowed.2
    obtain ⟨after,step,post⟩ := trust.borrow_frame n h
      (.shared (m.handle index) token owner) related valid enabled
    simp only [run,if_neg no] at step post
    exact ⟨.Err _,sdk,after,ran,step,post,image⟩
  · rcases success with ⟨next,rfl,lower,upper,increment,rfl⟩
    have allowed : 0 ≤ h.counter (h.accounts (m.handle index)).1 ∧
        h.counter (h.accounts (m.handle index)).1 < maxCounter := by
      rw [handle,counter]
      constructor
      · exact lower
      · change cell.borrowed.val < (core.num.Isize.MAX : Isize).val at upper
        rwa [isize64] at upper
    obtain ⟨after,step,post⟩ := trust.shared_ok n h (m.handle index) token owner
      related valid enabled allowed.1 allowed.2
    rw [handle] at post
    exact ⟨.Ok (),setCounter sdk account.data_slot cell next,after,ran,step,post,
      image_shared_acquire m h sdk image account.data_slot cell next token owner read increment⟩

#print axioms shared_reference_port
#print axioms shared_sdk_step
end AspisR1.S2H
