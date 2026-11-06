import NKY_BoxTotal
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKY_BoxPost
open Aeneas Aeneas.Std Result
open NKY_BoxAction
open NKY_BoxFrame (Heap install)
/-- Projection of the SAME post-call reads at every previously live typed
place. Non-live places are outside the caller-visible footprint. -/
def old {T : Type} (before : Heap T) (readsAfter : Nat → T) : Heap T :=
 fun address=>match before address with | none=>none | some _=>some (readsAfter address)
def observed {T : Type} (before : Heap T) (readsAfter : Nat → T)
 (out : core.result.Result (Owned T) PE) : Heap T :=
 match out with
 | .Err _ => old before readsAfter
 | .Ok box => fun address=>if address=box.owner then some box.value else old before readsAfter address

def model {T : Type} (before : Heap T) : core.result.Result (Owned T) PE → Heap T
 | .Err _ => before
 | .Ok box => install before box

def Readonly {T : Type} (W : T → T → Prop) (before : Heap T) (readsAfter : Nat → T) : Prop :=
 ∀ address value,before address=some value→W value (readsAfter address)
def Allocated {T : Type} (W : T → T → Prop) (before : Heap T) (readsAfter : Nat → T)
 (owner : Nat) : Prop :=
 ∀ address value,before address=some value→address≠owner→W value (readsAfter address)

/-- K015/K018's arbitrary pre-existing Box, typed field and coordinate;
mutation K016/K019 and alias K017/K020 controls. W is exactly the NKP six/
fourteen field-window predicate. Source and assertion hashes are in
NKY_CERTIFICATES.json. No poststate endpoint equation is in this cut. -/
def Windows {T F S : Type} (W : T → T → Prop)
 (a : S2W_D189Wrappers.Allocator S) (s : S) (bytes : Nat)
 (r : NP6_StdModel.Reservation) (raw : core.result.Result T F)
 (box : Owned T) (before : Heap T) (readsAfter : Nat → T) : Prop :=
 match raw with
 | .Err _ => Readonly W before readsAfter
 | .Ok _ =>
  match a.allocate s bytes,r with
  | .ok _,.Ok _ => Allocated W before readsAfter box.owner
  | _,_ => True

theorem old_eq {T : Type} (before : Heap T) (readsAfter : Nat → T)
 (h : Readonly (fun a b=>b=a) before readsAfter) : old before readsAfter=before := by
 funext address
 cases hb:before address with
 | none => simp [old,hb]
 | some value => simp [old,hb,h address value hb]

theorem observed_eq {T : Type} (before : Heap T) (readsAfter : Nat → T) (box : Owned T)
 (h : Allocated (fun a b=>b=a) before readsAfter box.owner) :
 observed before readsAfter (.Ok box)=model before (.Ok box) := by
 funext address
 by_cases he:address=box.owner
 · simp [observed,model,install,he]
 · cases hb:before address with
   | none => simp [observed,model,install,he,old,hb]
   | some value => simp [observed,model,install,he,old,hb,h address value hb he]

/-- The actual owned carrier, actual allocator post, and actual caller-visible
post reads are returned in ONE Result. This is a post-cut summary of the
single wrapper call, not a second allocation or a separately chosen frame. -/
def native {T F S : Type} (a : S2W_D189Wrappers.Allocator S) (s : S)
 (bytes : Nat) (r : NP6_StdModel.Reservation) (raw : core.result.Result T F)
 (box : Owned T) (before : Heap T) (readsAfter : Nat → T) :
 Result (core.result.Result (Owned T) PE × S × Heap T) := do
 let (out,post) ← NKY_BoxTotal.native a s bytes r raw box
 ok (out,post,observed before readsAfter out)

def attach {T S : Type} (before : Heap T)
 (result : Result (core.result.Result (Owned T) PE × S)) :
 Result (core.result.Result (Owned T) PE × S × Heap T) := do
 let (out,post) ← result
 ok (out,post,model before out)

theorem association {T F S : Type} (a : S2W_D189Wrappers.Allocator S) (s : S)
 (bytes : Nat) (r : NP6_StdModel.Reservation) (raw : core.result.Result T F)
 (box : Owned T) (before : Heap T) (readsAfter : Nat → T)
 (cut : Windows (fun a b=>b=a) a s bytes r raw box before readsAfter) :
 native a s bytes r raw box before readsAfter=
 attach before (NKY_BoxTotal.native a s bytes r raw box) := by
 cases raw with
 | Err e =>
  have h : Readonly (fun a b=>b=a) before readsAfter := cut
  simp [native,attach,NKY_BoxTotal.native,observed,model,old_eq before readsAfter h]
 | Ok value =>
  cases ha:a.allocate s bytes with
  | fail e => simp [native,attach,NKY_BoxTotal.native,ha]
  | div => simp [native,attach,NKY_BoxTotal.native,ha]
  | ok post =>
   cases r with
   | Err e => simp [native,attach,NKY_BoxTotal.native,ha]
   | Ok unit =>
    cases unit
    have h : Allocated (fun a b=>b=a) before readsAfter box.owner := by
     simpa only [Windows,ha] using cut
    simp [native,attach,NKY_BoxTotal.native,ha,observed_eq before readsAfter box h]
#print axioms old_eq
#print axioms observed_eq
#print axioms association
end AspisR1.NKY_BoxPost
end
