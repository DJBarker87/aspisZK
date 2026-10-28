import Aeneas.Std.SliceIter
import Lean.Elab.Tactic.Omega

/-! Owned operational boundary for the sized, shared slice iterator used by
V240. Addresses include allocation identity; casts do not erase provenance.
The source binding must separately establish the native representation relation.
No claim about arbitrary raw-pointer dereferences or allocation is made here. -/
namespace R1Z.PV_RDB2_Pointer
set_option autoImplicit false
open Aeneas Aeneas.Std Result

structure Pointer where
  allocation : Nat
  address : Nat
  deriving DecidableEq

structure NonNull where
  pointer : Pointer
  nonzero : pointer.address ≠ 0

/-- `repr(transparent)` encoding of an already valid non-null pointer. -/
def pack (p : Pointer) (h : p.address ≠ 0) : NonNull := ⟨p,h⟩

/-- The deployed body constructs the field after a sized pointer cast. -/
def cast (p : NonNull) : NonNull := ⟨p.pointer,p.nonzero⟩

theorem cast_complete (p : NonNull) (heap : List U32) :
    (ok (cast p,heap) : Result (NonNull × List U32)) = ok (p,heap) := rfl

theorem pack_projection (p : Pointer) (h : p.address ≠ 0) :
    (pack p h).pointer = p := rfl

structure Cursor where
  allocation : Nat
  base : Nat
  position : Nat
  values : Slice U32

def pointer (c : Cursor) : Pointer := ⟨c.allocation,c.base+4*c.position⟩
def endPointer (c : Cursor) : Pointer := ⟨c.allocation,c.base+4*c.values.val.length⟩
def valid (c : Cursor) : Prop :=
  0 < c.base ∧ c.position ≤ c.values.val.length ∧
  c.base+4*c.values.val.length < 2^64 ∧ 4*c.values.val.length < 2^63

def advance (c : Cursor) : Cursor := {c with position := c.position+1}
def abstract (c : Cursor) : core.slice.iter.Iter U32 := ⟨c.values,c.position⟩

/-- Non-ZST branch of deployed `Iter::next`, including unchanged storage.
Out-of-bounds is undefined, so only `valid` cursors are source-related. -/
def next (c : Cursor) : Result (Option U32 × Cursor) :=
  if pointer c = endPointer c then ok (none,c)
  else if h : c.position < c.values.val.length then
    ok (some c.values.val[c.position],advance c)
  else fail .undef

theorem pointer_eq_end (c : Cursor) :
    pointer c = endPointer c ↔ c.position = c.values.val.length := by
  simp only [pointer,endPointer,Pointer.mk.injEq,true_and]
  omega

theorem advance_address (c : Cursor) :
    pointer (advance c) = ⟨(pointer c).allocation,(pointer c).address+4⟩ := by
  simp only [pointer,advance,Pointer.mk.injEq,true_and]
  omega

theorem advance_valid (c : Cursor) (hv : valid c)
    (h : c.position < c.values.val.length) : valid (advance c) := by
  rcases hv with ⟨hb,hp,he,hs⟩
  exact ⟨hb,by simp only [advance]; omega,he,hs⟩

theorem read_bounds (c : Cursor) (hv : valid c)
    (h : c.position < c.values.val.length) :
    0 < (pointer c).address ∧
    (pointer c).address+4 ≤ (endPointer c).address ∧
    (pointer c).address+4 < 2^64 := by
  rcases hv with ⟨hb,hp,he,hs⟩
  simp only [pointer,endPointer]
  omega

/-- Complete Result and iterator post-state simulation, not output equality. -/
theorem next_complete (c : Cursor) (hv : valid c) :
    (do let (value,c') ← next c; ok (value,abstract c')) =
      core.slice.iter.IteratorSliceIter.next (abstract c) := by
  rcases hv with ⟨hb,hp,he,hs⟩
  by_cases h : c.position < c.values.val.length
  · have hn : pointer c ≠ endPointer c := by
      intro eq; have := (pointer_eq_end c).mp eq; omega
    simp only [next,hn,↓reduceIte,h,abstract,advance,bind_tc_ok,
      core.slice.iter.IteratorSliceIter.next]
    simp only [Slice.len_val,Slice.length,h,↓reduceDIte,Slice.getElem_Nat_eq]
    rfl
  · have eq : pointer c = endPointer c := (pointer_eq_end c).mpr (by omega)
    simp only [next,eq,↓reduceIte,abstract,bind_tc_ok,
      core.slice.iter.IteratorSliceIter.next,Slice.len_val,Slice.length,h,↓reduceDIte]

/-- A shared next never changes the backing slice, including exhaustion. -/
theorem next_storage (c : Cursor) (hv : valid c) :
    ∃ value c', next c = ok (value,c') ∧ c'.values = c.values ∧
      c'.allocation = c.allocation ∧ c'.base = c.base ∧ valid c' := by
  by_cases h : c.position < c.values.val.length
  · have hn : pointer c ≠ endPointer c := by
      intro eq; have := (pointer_eq_end c).mp eq; omega
    exact ⟨some c.values.val[c.position],advance c,
      by simp only [next,hn,↓reduceIte,h,↓reduceDIte],rfl,rfl,rfl,advance_valid c hv h⟩
  · have eq : pointer c = endPointer c := (pointer_eq_end c).mpr (by
      have := hv.2.1; omega)
    exact ⟨none,c,by simp only [next,eq,↓reduceIte],rfl,rfl,rfl,hv⟩

#print axioms cast_complete
#print axioms pack_projection
#print axioms pointer_eq_end
#print axioms advance_address
#print axioms advance_valid
#print axioms read_bounds
#print axioms next_complete
#print axioms next_storage
end R1Z.PV_RDB2_Pointer
