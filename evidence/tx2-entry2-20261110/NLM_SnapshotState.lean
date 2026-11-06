import NLM_SnapshotBridge
import NJU_Log
set_option autoImplicit false
noncomputable section
namespace NLM_Snapshot
open Aeneas Aeneas.Std Result AspisR1 AspisR1.S2W_D189Entry
open NLF_RefCell NLF_SdkModel
abbrev Owned := AdapterRw.r1_pool_adapter.owned.OwnedAccount
/-- A snapshot abort retains the live guard in its last event. It must not
be replaced by the normal-return bracket, which has already released it. -/
structure State where
 input : Entry
 sdk : NLF_SdkModel.State
 next : Nat := 0
 owned : List Owned := []
inductive Event where
 | acquire (before : State) (account token : Nat) (post : NLF_SdkModel.State)
   (reply : Result (Except ProgramError Guard))
 | deref (before : State) (guard : Guard) (payload : Result Payload)
 | allocate (before : State) (guard : Guard) (length : Nat) (reply : Result Unit)
 | release (before : State) (guard : Guard) (reply : Result (Except NLF_RefCell.Error NLF_SdkModel.State))
 | returned (before : State) (account lo hi : Nat) (value : Result Owned)
abbrev Run (A : Type) := NJU_Log.Run Event A
/-- Std allocator result at THIS to_vec occurrence, still to be bound to the
approved allocator interpretation by the enclosing native cut. Not a row root. -/
def G (s : State) (account lo hi : Nat) (allocation : Result Unit) : Run (Owned × State) := do
 let acquisition := try_borrow_data s.sdk account s.next
 let guardReply ← NJU_Log.record (.acquire s account s.next acquisition.1) (.ok acquisition.2)
 match guardReply with
 | .error _ =>
   let value := {(s.input.snapshot account lo hi) with
     length := .Err .AccountBorrowFailed,bytes := .Err .AccountBorrowFailed}
   let _ ← NJU_Log.record (.returned s account lo hi) (.ok value)
   pure (value,{s with next := s.next+1,owned := s.owned++[value]})
 | .ok g =>
   let live := {s with sdk := acquisition.1,next := s.next+1}
   let payload ← NJU_Log.record (.deref live g) (.ok (deref acquisition.1 g))
   let allowed := payload.bytes.length=lo ∨ payload.bytes.length=hi
   if allowed then
     let _ ← NJU_Log.record (.allocate live g payload.bytes.length) allocation
     pure ()
   else pure ()
   let dropped ← NJU_Log.record (.release live g) (.ok (release acquisition.1 g))
   match dropped with
   | .error _ => liftM (Result.fail .panic : Result (Owned × State))
   | .ok restored =>
     let value := s.input.snapshot account lo hi
     let _ ← NJU_Log.record (.returned live account lo hi) (.ok value)
     pure (value,{s with sdk := restored,next := s.next+1,owned := s.owned++[value]})
#print G
end NLM_Snapshot
