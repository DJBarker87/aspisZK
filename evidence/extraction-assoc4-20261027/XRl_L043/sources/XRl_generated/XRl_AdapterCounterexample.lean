import XRl_Adapter
open Aeneas Aeneas.Std Result
open XRk_Release
namespace XRl_Adapter
/-- A mutable Rust slice iterator represents the unconsumed interval [i,len).
On next_back it must return None when i=len, including after a prior next.
This reference uses the same pinned shared next_back with the ACTUAL cursor,
instead of replacing that cursor by zero. Rust core/src/slice/iter/macros.rs,
DoubleEndedIterator::next_back: is_empty! before pre_dec_end(1). -/
def originalNextBackValue {T : Type} (s : core.slice.iter.IterMut T) : Result (Option T) := do
  let (v,_) ← core.slice.iter.Iter.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedT.next_back
    (⟨s.slice,s.i⟩ : core.slice.iter.Iter T)
  ok v

def adaptedNextBackValue {T : Type} (s : core.slice.iter.IterMut T) : Result (Option T) := do
  let (v,_) ← XRk_nextBackPair s
  ok v

def exhausted : core.slice.iter.IterMut Bool :=
  ⟨⟨[true],by scalar_tac⟩,1⟩

theorem exhausted_original : originalNextBackValue exhausted = ok none := by rfl

theorem exhausted_adapted : adaptedNextBackValue exhausted = ok (some true) := by rfl

/-- A concrete well-formed exhausted iterator refutes the all-input value
claim, before any final-state comparison is attempted. -/
theorem next_back_not_equivalent :
    adaptedNextBackValue exhausted ≠ originalNextBackValue exhausted := by
  rw [exhausted_adapted,exhausted_original]
  intro h
  cases h

/-- This is a reachable library iterator state: one successful forward next
on a singleton, with no mutation of the yielded borrow. -/
theorem exhausted_reachable :
    ∃ back, core.slice.iter.IteratorIterMut.next
      (⟨exhausted.slice,0⟩ : core.slice.iter.IterMut Bool) = ok (some true,exhausted,back) := by
  exact ⟨_,rfl⟩

#print axioms exhausted_original
#print axioms exhausted_adapted
#print axioms next_back_not_equivalent
#print axioms exhausted_reachable
end XRl_Adapter
