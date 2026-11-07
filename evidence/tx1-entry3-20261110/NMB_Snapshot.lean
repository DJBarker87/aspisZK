import NMB_Input
import NJU_Log
set_option autoImplicit false
noncomputable section
namespace NMB_Snapshot
open Aeneas Aeneas.Std Result AspisR1 NLF_RefCell NLF_SdkModel
abbrev Owned := NMB_Input.Owned
/-- Parent state: original per-occurrence descriptors, SDK cells, globally
advancing token identity and the owned prefix constructed so far. -/
structure State where
 input : NMB_Input.Input
 sdk : NLF_SdkModel.State
 next : Nat
 owned : List Owned
inductive Event where
 | acquire (before : State) (account token : Nat) (post : NLF_SdkModel.State)
   (reply : Result (Except ProgramError Guard))
 | deref (before : State) (guard : Guard) (payload : Result Payload)
 | allocate (before : State) (guard : Guard) (length : Nat) (reply : Result Unit)
 | release (before : State) (guard : Guard)
   (reply : Result (Except NLF_RefCell.Error NLF_SdkModel.State))
 | returned (before : State) (account lo hi : Nat) (value : Result Owned)
abbrev Run (A : Type) := NJU_Log.Run Event A
/-- Line-faithful snapshot transcription. The input-byte association is a
caller clause on the original input and SAME SDK cells, never a chosen output. -/
def G (s : State) (a lo hi : Nat) (allocation : Result Unit) : Run (Owned × State) := do
 let acquisition := try_borrow_data s.sdk a s.next
 let guardReply ← NJU_Log.record (.acquire s a s.next acquisition.1) (.ok acquisition.2)
 match guardReply with
 | .error _ =>
   let value := {(s.input.descriptors a) with
     length := .Err .AccountBorrowFailed,bytes := .Err .AccountBorrowFailed}
   let _ ← NJU_Log.record (.returned s a lo hi) (.ok value)
   pure (value,{s with next:=s.next+1,owned:=s.owned++[value]})
 | .ok g =>
   let live := {s with sdk:=acquisition.1,next:=s.next+1}
   let payload ← NJU_Log.record (.deref live g) (.ok (deref acquisition.1 g))
   if payload.bytes.length=lo ∨ payload.bytes.length=hi then
     let _ ← NJU_Log.record (.allocate live g payload.bytes.length) allocation
     pure ()
   else pure ()
   let dropped ← NJU_Log.record (.release live g) (.ok (release acquisition.1 g))
   match dropped with
   | .error _ => liftM (Result.fail .panic : Result (Owned × State))
   | .ok restored =>
     let value := s.input.snapshot a lo hi
     let _ ← NJU_Log.record (.returned live a lo hi) (.ok value)
     pure (value,{s with sdk:=restored,next:=s.next+1,owned:=s.owned++[value]})
def ready (x : NMB_Input.Input) (t : Nat) (owned : List Owned) : State :=
 ⟨x,x.sdk,t,owned⟩
def guard (s : State) (a : Nat) : Guard := ⟨(s.sdk.accounts a).data,s.next,.shared⟩
def acquired (s : State) (a : Nat) : NLF_SdkModel.State :=
 put s.sdk (s.sdk.accounts a).data
  {s.sdk.cells (s.sdk.accounts a).data with readers:=s.next::(s.sdk.cells (s.sdk.accounts a).data).readers}
def live (s : State) (a : Nat) : State := {s with sdk:=acquired s a,next:=s.next+1}
def returned (s : State) (a lo hi : Nat) : State :=
 {s with next:=s.next+1,owned:=s.owned++[s.input.snapshot a lo hi]}
#print State
#print G
end NMB_Snapshot
