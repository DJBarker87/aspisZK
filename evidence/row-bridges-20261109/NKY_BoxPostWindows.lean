import NKY_BoxPost
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKY_FrameObservation
open Aeneas Aeneas.Std
/-- Native u8/u32/u64 fields are widened to u64; their natural values are
unchanged. Booleans use the explicit0/1image below. -/
def bit (x : Bool) : Nat := if x then 1 else 0
theorem bit_injective : Function.Injective bit := by
 intro a b h
 cases a <;> cases b <;> simp_all [bit]
def readImage {T : Type} {n : Usize} (image : T → Nat) (a : Array T n) (i : Nat) : Nat :=
 ((a.val[i]?).map image).getD 0
theorem at_injective {T : Type} {n : Usize} (image : T → Nat)
 (injective : Function.Injective image) (a b : Array T n) (i : Nat) (hi : i<n.val)
 (h : readImage image a i=readImage image b i) : a.val[i]?=b.val[i]? := by
 have ha : i<a.val.length := by rw [a.property];exact hi
 have hb : i<b.val.length := by rw [b.property];exact hi
 simp only [readImage,List.getElem?_eq_getElem ha,List.getElem?_eq_getElem hb,Option.map_some,Option.getD_some] at h
 rw [List.getElem?_eq_getElem ha,List.getElem?_eq_getElem hb]
 exact congrArg some (injective h)

def checkpoint (a : NJQ_Carrier.CC) (tag i : Nat) : Nat :=
 match tag with
 | 0 => a.bump.val
 | 1 => readImage (fun x=>x.val) a.master i
 | 2 => readImage (fun x=>x.val) a.deployment_domain i
 | 3 => a.checkpoint_sequence.val
 | 4 => readImage (fun x=>x.val) a.global_root (i%8)
 | _ => readImage (fun x=>x.val) a.lane_sequences (i%8)
def master (a : NJQ_Carrier.CM) (tag i : Nat) : Nat :=
 match tag with
 | 0 => a.bump.val
 | 1 => readImage (fun x=>x.val) a.identity.pool i
 | 2 => readImage (fun x=>x.val) a.identity.asset_mint i
 | 3 => readImage (fun x=>x.val) a.identity.token_program i
 | 4 => a.identity.asset_id.val
 | 5 => readImage (fun x=>x.val) a.identity.deployment_domain i
 | 6 => a.verifier_policy.flags.val
 | 7 => readImage (fun x=>x.val) a.verifier_policy.registry_program i
 | 8 => readImage (fun x=>x.val) a.verifier_policy.registry_authority i
 | 9 => readImage (fun x=>x.val) a.verifier_policy.policy_binding i
 | 10 => a.initialized_lane_mask.val
 | 11 => bit a.has_checkpoint
 | 12 => a.next_checkpoint_sequence.val
 | _ => readImage (fun x=>x.val) a.last_checkpoint_lane_sequences (i%8)
def Checkpoint (a b : NJQ_Carrier.CC) : Prop :=
 ∀ tag i,tag<6→i<32→checkpoint a tag i=checkpoint b tag i
def Master (a b : NJQ_Carrier.CM) : Prop :=
 ∀ tag i,tag<14→i<32→master a tag i=master b tag i

theorem checkpoint_windows (a b : NJQ_Carrier.CC) (h : Checkpoint a b) :
 NKF_Windows.Checkpoint a b := by
 refine ⟨UScalar.eq_of_val_eq (h 0 0 (by decide) (by decide)),?_,?_,
  UScalar.eq_of_val_eq (h 3 0 (by decide) (by decide)),?_,?_⟩
 · intro i hi
   exact at_injective _ (fun _ _ e=>UScalar.eq_of_val_eq e) _ _ i hi (h 1 i (by decide) hi)
 · intro i hi
   exact at_injective _ (fun _ _ e=>UScalar.eq_of_val_eq e) _ _ i hi (h 2 i (by decide) hi)
 · intro i hi
   exact at_injective _ (fun _ _ e=>UScalar.eq_of_val_eq e) _ _ (i%8) (by exact Nat.mod_lt _ (by decide)) (h 4 i (by decide) hi)
 · intro i hi
   exact at_injective _ (fun _ _ e=>UScalar.eq_of_val_eq e) _ _ (i%8) (by exact Nat.mod_lt _ (by decide)) (h 5 i (by decide) hi)

theorem master_windows (a b : NJQ_Carrier.CM) (h : Master a b) :
 NKF_Windows.Master a b := by
 refine ⟨UScalar.eq_of_val_eq (h 0 0 (by decide) (by decide)),?_,?_,?_,
  UScalar.eq_of_val_eq (h 4 0 (by decide) (by decide)),?_,
  UScalar.eq_of_val_eq (h 6 0 (by decide) (by decide)),?_,?_,?_,
  UScalar.eq_of_val_eq (h 10 0 (by decide) (by decide)),
  bit_injective (h 11 0 (by decide) (by decide)),
  UScalar.eq_of_val_eq (h 12 0 (by decide) (by decide)),?_⟩
 · intro i hi;exact at_injective _ (fun _ _ e=>UScalar.eq_of_val_eq e) _ _ i hi (h 1 i (by decide) hi)
 · intro i hi;exact at_injective _ (fun _ _ e=>UScalar.eq_of_val_eq e) _ _ i hi (h 2 i (by decide) hi)
 · intro i hi;exact at_injective _ (fun _ _ e=>UScalar.eq_of_val_eq e) _ _ i hi (h 3 i (by decide) hi)
 · intro i hi;exact at_injective _ (fun _ _ e=>UScalar.eq_of_val_eq e) _ _ i hi (h 5 i (by decide) hi)
 · intro i hi;exact at_injective _ (fun _ _ e=>UScalar.eq_of_val_eq e) _ _ i hi (h 7 i (by decide) hi)
 · intro i hi;exact at_injective _ (fun _ _ e=>UScalar.eq_of_val_eq e) _ _ i hi (h 8 i (by decide) hi)
 · intro i hi;exact at_injective _ (fun _ _ e=>UScalar.eq_of_val_eq e) _ _ i hi (h 9 i (by decide) hi)
 · intro i hi;exact at_injective _ (fun _ _ e=>UScalar.eq_of_val_eq e) _ _ (i%8) (by exact Nat.mod_lt _ (by decide)) (h 13 i (by decide) hi)
#print axioms bit_injective
#print axioms at_injective
#print axioms checkpoint_windows
#print axioms master_windows
end AspisR1.NKY_FrameObservation

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
 (cut : NKY_BoxPost.Windows NKY_FrameObservation.Checkpoint a s 176 r raw box before readsAfter) :
 NKY_BoxPost.Windows (fun a b=>b=a) a s 176 r raw box before readsAfter :=
 lift _ (fun x y h=>(NKF_BoxFields.checkpoint x y (NKF_Windows.checkpoint_fields x y (NKY_FrameObservation.checkpoint_windows x y h))).symm)
  a s 176 r raw box before readsAfter cut

theorem master {S : Type} (a : S2W_D189Wrappers.Allocator S) (s : S)
 (r : NP6_StdModel.Reservation) (raw : core.result.Result NJQ_Carrier.CM NJQ_Carrier.CF)
 (box : Owned NJQ_Carrier.CM) (before : Heap NJQ_Carrier.CM) (readsAfter : Nat → NJQ_Carrier.CM)
 (cut : NKY_BoxPost.Windows NKY_FrameObservation.Master a s 304 r raw box before readsAfter) :
 NKY_BoxPost.Windows (fun a b=>b=a) a s 304 r raw box before readsAfter :=
 lift _ (fun x y h=>(NKF_BoxFields.master x y (NKF_Windows.master_fields x y (NKY_FrameObservation.master_windows x y h))).symm)
  a s 304 r raw box before readsAfter cut
#print axioms lift
#print axioms checkpoint
#print axioms master
end AspisR1.NKY_BoxPostWindows
end
