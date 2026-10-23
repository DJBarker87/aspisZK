import S2TrustedSdkBorrow

/-! D157 / continuation-2 authorization: one pure slice primitive. A source
slice is a retained value, not an invented alias of the destination allocation.
The carrier includes the entire ambient state, so the field licenses no
allocator, SDK, syscall, helper or caller effect. -/
set_option autoImplicit false
namespace AspisR1.S2W_TrustedStd
open S2Trust

inductive Outcome (F : Type) where
  | returned (heap : Heap F)
  | panic

/-- Copy exactly the accessible destination range; preserve descriptor and
inaccessible contents. The source is evaluated before the destination write. -/
def copied (dst src : Payload) : Payload :=
  {dst with contents := fun i => if i < dst.descriptor.length then src.contents i else dst.contents i}

def copyHeap {F : Type} (s : Heap F) (dst : Nat) (src : Payload) : Heap F :=
  {s with payload := put s.payload dst (copied (s.payload dst) src)}

def specification {F : Type} (s : Heap F) (dst : Nat) (src : Payload) : Outcome F :=
  if (s.payload dst).descriptor.length = src.descriptor.length
  then .returned (copyHeap s dst src) else .panic

/-- Exactly one added trust field. `copy` is the interpreted native
slice::copy_from_slice operation on valid exclusive dst/shared src slices.
Its domain excludes invalid Rust references; reference admission is the SDK /
runtime boundary, not an additional std behavior. Equal lengths copy; unequal
lengths panic; the only state change is destination contents. -/
structure TrustedStd {F : Type}
    (copy : Heap F → Nat → Payload → Outcome F) : Prop where
  slice_copy_from_slice : ∀ s dst src, copy s dst src = specification s dst src

/-- Consistency witness only; no production-library instance is asserted. -/
theorem specification_satisfies (F : Type) :
    TrustedStd (specification (F := F)) := ⟨fun _ _ _ => rfl⟩

/-- A proved per-cell contract composes by function extensionality. Outside
length is framed as well; no finite enumeration or concrete buffer reduction. -/
theorem cells_compose (dst src after : Payload)
    (descriptor : after.descriptor = dst.descriptor)
    (cells : ∀ i, after.contents i =
      if i < dst.descriptor.length then src.contents i else dst.contents i) :
    after = copied dst src := by
  cases after with
  | mk desc contents =>
    simp only at descriptor cells
    subst desc
    have same : contents = (copied dst src).contents := funext cells
    cases dst
    simp only [copied] at same ⊢
    cases same
    rfl

theorem accepted_copy {F : Type} (copy : Heap F → Nat → Payload → Outcome F)
    (std : TrustedStd copy) (s : Heap F) (dst : Nat) (src : Payload)
    (lengths : (s.payload dst).descriptor.length = src.descriptor.length) :
    copy s dst src = .returned (copyHeap s dst src) := by
  rw [std.slice_copy_from_slice, specification, if_pos lengths]

theorem mismatched_copy {F : Type} (copy : Heap F → Nat → Payload → Outcome F)
    (std : TrustedStd copy) (s : Heap F) (dst : Nat) (src : Payload)
    (lengths : (s.payload dst).descriptor.length ≠ src.descriptor.length) :
    copy s dst src = .panic := by
  rw [std.slice_copy_from_slice, specification, if_neg lengths]

/-- Full ambient/account/borrow/allocator frame plus every other payload. -/
theorem copy_frame {F : Type} (s : Heap F) (dst : Nat) (src : Payload) :
    (copyHeap s dst src).ambient = s.ambient ∧
    (copyHeap s dst src).accounts = s.accounts ∧
    (copyHeap s dst src).counter = s.counter ∧
    (copyHeap s dst src).external = s.external ∧
    (copyHeap s dst src).guards = s.guards ∧
    (copyHeap s dst src).allocated = s.allocated ∧
    (copyHeap s dst src).ownerLive = s.ownerLive ∧
    (∀ c, ((copyHeap s dst src).payload c).descriptor = (s.payload c).descriptor) ∧
    (∀ c, c ≠ dst → (copyHeap s dst src).payload c = s.payload c) := by
  refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_,?_⟩
  · intro c
    by_cases h : c = dst <;> simp [copyHeap,put,copied,h]
  · intro c h
    simp [copyHeap,put,h]

#print axioms specification_satisfies
#print axioms cells_compose
#print axioms accepted_copy
#print axioms mismatched_copy
#print axioms copy_frame
end AspisR1.S2W_TrustedStd
