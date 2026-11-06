import NKY_BoxPost
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKY_BoxPostWindows
open Aeneas Aeneas.Std Result
open NKY_BoxAction
open NKY_BoxFrame (Heap)
/-- Reconstruct every old live cell from the native typed window assertions;
the full post-heap equality is derived later, never an input assumption. -/
theorem lift {T F S : Type} (W : T → T → Prop)
 (ext : ∀ a b,W a b→b=a) (a : S2W_D189Wrappers.Allocator S) (s : S)
 (bytes : Nat) (r : NP6_StdModel.Reservation) (raw : core.result.Result T F)
 (box : Owned T) (before : Heap T) (readsAfter : Nat → T)
 (cut : NKY_BoxPost.Windows W a s bytes r raw box before readsAfter) :
 NKY_BoxPost.Windows (fun a b=>b=a) a s bytes r raw box before readsAfter := by
 cases raw with
 | Err e =>
  intro address value hb
  exact ext _ _ (cut address value hb)
 | Ok value =>
  cases ha:a.allocate s bytes <;> cases r <;> simp only [NKY_BoxPost.Windows,ha] <;> try trivial
  have h : NKY_BoxPost.Allocated W before readsAfter box.owner := by
   simpa only [NKY_BoxPost.Windows,ha] using cut
  intro address old hb he
  exact ext _ _ (h address old hb he)

theorem checkpoint {S : Type} (a : S2W_D189Wrappers.Allocator S) (s : S)
 (r : NP6_StdModel.Reservation) (raw : core.result.Result NJQ_Carrier.CC NJQ_Carrier.CF)
 (box : Owned NJQ_Carrier.CC) (before : Heap NJQ_Carrier.CC) (readsAfter : Nat → NJQ_Carrier.CC)
 (cut : NKY_BoxPost.Windows NKF_Windows.Checkpoint a s 176 r raw box before readsAfter) :
 NKY_BoxPost.Windows (fun a b=>b=a) a s 176 r raw box before readsAfter :=
 lift _ (fun x y h=>(NKF_BoxFields.checkpoint x y (NKF_Windows.checkpoint_fields x y h)).symm)
  a s 176 r raw box before readsAfter cut

theorem master {S : Type} (a : S2W_D189Wrappers.Allocator S) (s : S)
 (r : NP6_StdModel.Reservation) (raw : core.result.Result NJQ_Carrier.CM NJQ_Carrier.CF)
 (box : Owned NJQ_Carrier.CM) (before : Heap NJQ_Carrier.CM) (readsAfter : Nat → NJQ_Carrier.CM)
 (cut : NKY_BoxPost.Windows NKF_Windows.Master a s 304 r raw box before readsAfter) :
 NKY_BoxPost.Windows (fun a b=>b=a) a s 304 r raw box before readsAfter :=
 lift _ (fun x y h=>(NKF_BoxFields.master x y (NKF_Windows.master_fields x y h)).symm)
  a s 304 r raw box before readsAfter cut
#print axioms lift
#print axioms checkpoint
#print axioms master
end AspisR1.NKY_BoxPostWindows
end
