import Port23PUSH_Source
set_option autoImplicit false
noncomputable section
namespace Port25ARRAY
open Aeneas Aeneas.Std Result
abbrev Iter (T : Type) := core.slice.iter.IterMut T

/-- Literal array -> mutable slice -> iter_mut delegation, with the caller's
transformer continuation applied to the original iterator before readback.
No backend registration or native association is installed. -/
def arrayIntoIter {T : Type} {N : Usize} (a : Array T N) :
    Result (Iter T × ((Iter T → Iter T) → Array T N)) := do
  let (s, arrayBack) ← lift (Array.to_slice_mut a)
  let (it, sliceBack) ← core.slice.Slice.iter_mut s
  ok (it, fun transform => arrayBack (sliceBack (transform it)))

theorem delegation {T : Type} {N : Usize} (a : Array T N) :
    arrayIntoIter a = ok (⟨a.to_slice,0⟩,
      fun transform => Array.from_slice a (transform ⟨a.to_slice,0⟩).slice) := by
  rfl

/-- Full back law includes the existing wrapper's fallback for malformed
transformers. Actual next/back closures preserve the slice length. -/
theorem back_carrier {T : Type} {N : Usize} (a : Array T N)
    (f : Iter T → Iter T) :
    (Array.from_slice a (f ⟨a.to_slice,0⟩).slice).val =
      if (f ⟨a.to_slice,0⟩).slice.val.length = N.val
      then (f ⟨a.to_slice,0⟩).slice.val else a.val := by
  simp only [Array.from_slice]
  split <;> rfl

theorem back_identity {T : Type} {N : Usize} (a : Array T N) :
    Array.from_slice a ((id : Iter T → Iter T) ⟨a.to_slice,0⟩).slice = a := by
  cases a
  simp [Array.from_slice, Array.to_slice]

/-- Concrete transformer ABI for the exact Port23 row carrier. -/
def concrete : Port23PUSH.ArrayIntoIter := arrayIntoIter

#print axioms arrayIntoIter
#print axioms delegation
#print axioms back_carrier
#print axioms back_identity
#print axioms concrete
end Port25ARRAY
end
