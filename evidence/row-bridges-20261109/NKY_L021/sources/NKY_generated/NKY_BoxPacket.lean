import NKY_BoxFrame
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKY_BoxPacket
open Aeneas Aeneas.Std Result
open NKY_BoxAction
/-- Complete allocation/post/cleanup/frame packet for one source invocation.
The outer allocator Result is scrutinized, never assumed successful. The
logical heap frame concerns every address other than this allocation's owner;
its native interpretation is the controlled allocation-identity/frame cut. -/
def Law {T S : Type} (a : S2W_D189Wrappers.Allocator S) (s : S)
 (bytes alignment : Nat) (r : NP6_StdModel.Reservation) (owner : Nat)
 (before : NKY_BoxFrame.Heap T) (decoded : Result (core.result.Result T PE)) : Prop :=
 match decoded with
 | .fail e => run a s bytes r owner decoded=fail e ∧ events a s bytes alignment r owner decoded=[]
 | .div => run a s bytes r owner decoded=div ∧ events a s bytes alignment r owner decoded=[]
 | .ok (.Err e) => run a s bytes r owner decoded=ok (.Err e,s) ∧ events a s bytes alignment r owner decoded=[]
 | .ok (.Ok value) =>
  match a.allocate s bytes with
  | .fail e => run a s bytes r owner decoded=fail e ∧
    events a s bytes alignment r owner decoded=[.allocate owner bytes alignment]
  | .div => run a s bytes r owner decoded=div ∧
    events a s bytes alignment r owner decoded=[.allocate owner bytes alignment]
  | .ok post =>
   match r with
   | .Err _ => run a s bytes r owner decoded=fail .panic ∧
     events a s bytes alignment r owner decoded=[.allocate owner bytes alignment,.exhausted]
   | .Ok _ => run a s bytes r owner decoded=ok (.Ok ⟨owner,value⟩,post) ∧
     events a s bytes alignment r owner decoded=[.allocate owner bytes alignment,.returned owner] ∧
     NKY_BoxFrame.install before ⟨owner,value⟩ owner=some value ∧
     ∀ address,address≠owner→NKY_BoxFrame.install before (⟨owner,value⟩ : Owned T) address=before address

theorem complete {T S : Type} (a : S2W_D189Wrappers.Allocator S) (s : S)
 (bytes alignment : Nat) (r : NP6_StdModel.Reservation) (owner : Nat)
 (before : NKY_BoxFrame.Heap T) (decoded : Result (core.result.Result T PE)) :
 Law a s bytes alignment r owner before decoded := by
 cases decoded with
 | fail e => exact ⟨rfl,rfl⟩
 | div => exact ⟨rfl,rfl⟩
 | ok raw =>
  cases raw with
  | Err e => exact ⟨rfl,rfl⟩
  | Ok value =>
   cases ha:a.allocate s bytes with
   | fail e => simp [Law,run,newBox,events,ha]
   | div => simp [Law,run,newBox,events,ha]
   | ok post =>
    cases r with
    | Err e => simp [Law,run,newBox,events,ha]
    | Ok unit =>
     cases unit
     simpa only [Law,ha] using NKY_BoxFrame.allocation_success a s post bytes alignment owner value before ha
#print axioms complete
end AspisR1.NKY_BoxPacket
end
