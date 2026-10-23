import S2H_SdkSteps
set_option autoImplicit false
open Aeneas Aeneas.Std Result AspisS2OwnedStage1
namespace AspisR1.S2H
open S2Trust S2E S2E_Reference.S2E_Reference

theorem checkpoint_reference_port (sdk : SDK) (guards : LiveGuards) (slot : Usize) :
    owned_acquire_checkpoint sdk guards slot =
      SdkReference.owned_acquire_checkpoint sdk guards slot := rfl

def checkpointHeap {F : Type} (h : Heap F) (cell token owner : Nat)
    (reply : core.result.Result Unit PE) : Heap F :=
  match reply with
  | .Ok _ => acquire h cell token owner .exclusive
  | .Err _ => h

/-- Stage1's exclusive acquisition, including its exact unchanged error state.
No bounds restriction on byte vectors; native SDK trust is the only library law.
This is a primitive port, not reachability of source line957. -/
theorem checkpoint_sdk_step {W Child Alloc Event : Type}
    (L : Library W (World Child Alloc Event)) (trust : S2TrustedSdkBorrow L)
    (m : AllocationMap) (n : W) (h : Heap (World Child Alloc Event)) (sdk : SDK)
    (related : L.related n h) (valid : Valid h) (image : HeapImage m h sdk)
    (index token owner : Nat) (account : OwnedAccount) (guards : LiveGuards)
    (readAccount : sdk.accounts.val[index]? = some account)
    (enabled : Enabled h (.exclusive (m.handle index) token owner)) :
    ∃ (reply : core.result.Result Unit PE) (out : SDK) (outGuards : LiveGuards) (after : W),
      owned_acquire_checkpoint sdk guards account.data_slot = ok (reply,out,outGuards) ∧
      L.run n (.exclusive (m.handle index) token owner) = (after,sharedReply token reply) ∧
      L.related after (checkpointHeap h (m.dataCell account.data_slot.val) token owner reply) ∧
      HeapImage m (checkpointHeap h (m.dataCell account.data_slot.val) token owner reply) out := by
  have bounds := (image.slots index account readAccount).1
  obtain ⟨cell,actual,ran⟩ :=
    SdkReference.BorrowTotal.checkpoint_acquire_total sdk guards account.data_slot bounds
  have read : sdk.data_cells.val[account.data_slot.val]? = some cell :=
    List.getElem?_eq_some_iff.mpr ⟨bounds,actual.symm⟩
  have counter := (image.data account.data_slot.val cell read).2.2.2.1
  have handle := congrArg Prod.fst (image.handles index account readAccount)
  rw [← checkpoint_reference_port] at ran
  by_cases free : cell.borrowed = 0#isize
  · have zero : h.counter (h.accounts (m.handle index)).1 = 0 := by
      rw [handle,counter,free]
      scalar_tac
    obtain ⟨after,step,post⟩ := trust.exclusive_ok n h (m.handle index) token owner
      related valid enabled zero
    rw [handle] at post
    have notDifferent : ¬ (cell.borrowed != 0#isize) := by simp only [free,bne_self_eq_false,Bool.false_eq_true,not_false_eq_true]
    rw [if_neg notDifferent] at ran
    exact ⟨.Ok (),setCounter sdk account.data_slot cell (-1)#isize,
      {guards with checkpoint := some account.data_slot},after,ran,step,post,
      image_exclusive_acquire m h sdk image account.data_slot cell token owner read⟩
  · have nonzero : h.counter (h.accounts (m.handle index)).1 ≠ 0 := by
      rw [handle,counter]
      intro zero
      apply free
      apply IScalar.eq_of_val_eq
      scalar_tac
    obtain ⟨after,step,post⟩ := trust.exclusive_err n h (m.handle index) token owner
      related valid enabled nonzero
    have different : (cell.borrowed != 0#isize) = true := bne_iff_ne.mpr free
    rw [if_pos different] at ran
    exact ⟨.Err _,sdk,guards,after,ran,step,post,image⟩

#print axioms checkpoint_reference_port
#print axioms checkpoint_sdk_step
end AspisR1.S2H
