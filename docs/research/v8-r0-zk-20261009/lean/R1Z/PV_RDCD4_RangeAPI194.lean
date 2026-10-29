import R1Z.PV_RDCD3_RangeFold
set_option autoImplicit false
namespace R1Z.PV_RDCD4_RangeAPI194
open Aeneas Aeneas.Std Result PV_RDCD3_RangeFold

structure Range where
  start : Nat
  stop : Nat
structure RangeIter where
  inner : Cursor

def fromRange (r : Range) : Cursor := ⟨r.start,r.stop⟩
def intoLegacy (r : Range) : Cursor := fromRange r
def intoIter (r : Range) : RangeIter := ⟨intoLegacy r⟩
def nextIter (r : RangeIter) : Option Nat × RangeIter :=
  let (value,inner) := next r.inner
  (value,⟨inner⟩)

theorem constructor (r : Range) :
    (intoIter r).inner=⟨r.start,r.stop⟩ := rfl

theorem next_binding (r : RangeIter) :
    (nextIter r).1=(next r.inner).1 ∧ (nextIter r).2.inner=(next r.inner).2 := by
  cases h : next r.inner with
  | mk value inner => simp [nextIter,h]

theorem active (r : RangeIter) (h : r.inner.start < r.inner.stop) :
    nextIter r=(some r.inner.start,⟨⟨r.inner.start+1,r.inner.stop⟩⟩) := by
  simp only [nextIter,next_active r.inner h]

theorem exhausted (r : RangeIter) (h : r.inner.stop ≤ r.inner.start) :
    nextIter r=(none,r) := by
  simp only [nextIter,next_empty r.inner h]

def wrappingAdd32 (a b : U32) : U32 := U32.wrapping_add a b
def wrappingSub32 (a b : U32) : U32 := U32.wrapping_sub a b
/-- The source library bodies forward to the compiler wrapping intrinsics.
The intrinsic arithmetic implementation remains the existing V370 boundary. -/
theorem add_forward (a b : U32) : wrappingAdd32 a b=core.num.U32.wrapping_add a b := rfl
theorem sub_forward (a b : U32) : wrappingSub32 a b=core.num.U32.wrapping_sub a b := rfl
#print axioms constructor
#print axioms next_binding
#print axioms active
#print axioms exhausted
#print axioms add_forward
#print axioms sub_forward
end R1Z.PV_RDCD4_RangeAPI194
