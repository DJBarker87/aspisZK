import NKY_BoxAction
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKY_BoxFrame
open Aeneas Aeneas.Std Result
open NKY_BoxAction
abbrev Heap (T : Type) := Nat → Option T

def install {T : Type} (before : Heap T) (box : Owned T) : Heap T :=
 fun address => if address=box.owner then some box.value else before address

theorem payload {T : Type} (before : Heap T) (owner : Nat) (value : T) :
 install before ⟨owner,value⟩ owner=some value := by simp [install]

theorem frame {T : Type} (before : Heap T) (box : Owned T) (address : Nat)
 (h : address≠box.owner) : install before box address=before address := by
 simp only [install,if_neg h]

/-- Native pointer identity is one conjunct; all payload fields must also be
reconstructed. Neither conjunct is inferred from the other. -/
theorem carrier_identity {T : Type} (box : Owned T) (owner : Nat) (value : T)
 (owner_cut : box.owner=owner) (payload_cut : box.value=value) : box=⟨owner,value⟩ := by
 cases box
 cases owner_cut
 cases payload_cut
 rfl

/-- No allocation/cleanup suffix after a raw decoder error, even for a rejected
reservation. This proves the frame at the same invocation's original state. -/
theorem decoder_error {T S : Type} (a : S2W_D189Wrappers.Allocator S) (s : S)
 (bytes alignment owner : Nat) (r : NP6_StdModel.Reservation) (e : PE) :
 run a s bytes r owner (ok (.Err e : core.result.Result T PE))=ok (.Err e,s) ∧
 events a s bytes alignment r owner (ok (.Err e : core.result.Result T PE))=[] := ⟨rfl,rfl⟩

theorem allocation_success {T S : Type} (a : S2W_D189Wrappers.Allocator S) (s post : S)
 (bytes alignment owner : Nat) (value : T) (before : Heap T)
 (h : a.allocate s bytes=ok post) :
 run a s bytes (.Ok ()) owner (ok (.Ok value))=ok (.Ok ⟨owner,value⟩,post) ∧
 events a s bytes alignment (.Ok ()) owner (ok (.Ok value))=
  [.allocate owner bytes alignment,.returned owner] ∧
 install before (⟨owner,value⟩ : Owned T) owner=some value ∧
 ∀ address,address≠owner→install before (⟨owner,value⟩ : Owned T) address=before address := by
 exact ⟨returning a s post bytes owner value h,by simp [events,h],payload before owner value,fun address ha=>frame before ⟨owner,value⟩ address ha⟩

/-- Full allocator fail/div prefixes have an allocation event and no later
return/cleanup event. The underlying allocator action is unchanged. -/
theorem allocation_abort {T S : Type} (a : S2W_D189Wrappers.Allocator S) (s : S)
 (bytes alignment owner : Nat) (value : T) (r : NP6_StdModel.Reservation)
 (h : ∀ post,a.allocate s bytes≠ok post) :
 events a s bytes alignment r owner (ok (.Ok value))=[.allocate owner bytes alignment] := by
 cases ha:a.allocate s bytes with
 | fail e => simp [events,ha]
 | div => simp [events,ha]
 | ok post => exact False.elim (h post ha)
#print axioms payload
#print axioms frame
#print axioms carrier_identity
#print axioms decoder_error
#print axioms allocation_success
#print axioms allocation_abort
end AspisR1.NKY_BoxFrame
end
