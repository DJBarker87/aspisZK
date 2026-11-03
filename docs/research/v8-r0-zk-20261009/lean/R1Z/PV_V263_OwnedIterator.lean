import R1Z.PV_V263_OwnedDrain
import R1Z.PV_V263_WorkerControl
/-! Front-only IntoIter used by the three deployed for loops. The allocation
base/capacity is distinct from the moving cursor. Exhaustion keeps the buffer
for DropGuard's RawVec deallocation; next itself cannot allocate or fault.
Pointer provenance, byte reads and native drop glue remain to be associated. -/
set_option autoImplicit false
namespace R1Z.PV_V263_OwnedIterator
open Aeneas Aeneas.Std PV_V263_World PV_V263_OwnedDrain

structure Iter (A : Type) where
  allocation : Allocation
  consumed : Nat
  remaining : List A
  fits : consumed+remaining.length≤capacity allocation

def intoIter {A : Type} (owner : Owner A) : Iter A :=
  ⟨owner.allocation,0,owner.initialized.values.val,
    by simpa only [Nat.zero_add,alloc.vec.Vec.length] using
      owner.initialized.fits.trans owner.reserved⟩

def pointer {A : Type} (iter : Iter A) : Nat :=
  iter.allocation.pointer+iter.consumed*iter.allocation.layout.size

def endPointer {A : Type} (iter : Iter A) : Nat :=
  if iter.allocation.layout.size=0 then (iter.allocation.pointer+iter.remaining.length) % (Usize.max+1)
  else iter.allocation.pointer+(iter.consumed+iter.remaining.length)*iter.allocation.layout.size

def next {A : Type} (iter : Iter A) : Option A × Iter A :=
  match h : iter.remaining with
  | [] => (none,iter)
  | a::rest => (some a,⟨iter.allocation,iter.consumed+1,rest,by
      have bound := iter.fits
      rw [h,List.length_cons] at bound
      omega⟩)

def deallocate {S : Type} (free : Nat → Nat → Nat → Q S Unit)
    (allocation : Allocation) : Q S Unit :=
  match release allocation with
  | none => PV_V263_World.lift (.ok ())
  | some (pointer,bytes,align) => free pointer bytes align

def dropValues {S A : Type} (dropValue : A → Q S Unit) : List A → Q S Unit
  | [] => PV_V263_World.lift (.ok ())
  | a::rest => PV_V263_World.bind (dropValue a) fun _ => dropValues dropValue rest

def drop {S A : Type} (dropValue : A → Q S Unit)
    (free : Nat → Nat → Nat → Q S Unit) (iter : Iter A) : Q S Unit :=
  PV_V263_WorkerControl.finalize .abort (dropValues dropValue iter.remaining)
    (deallocate free iter.allocation)

theorem moves {A : Type} (iter : Iter A) (a : A) (rest : List A)
    (h : iter.remaining=a::rest) :
    (next iter).1=some a ∧ (next iter).2.remaining=rest ∧
    (next iter).2.allocation=iter.allocation ∧
    (next iter).2.consumed=iter.consumed+1 := by
  cases iter with
  | mk allocation consumed remaining fits =>
    dsimp only at h
    subst remaining
    exact ⟨rfl,rfl,rfl,rfl⟩

theorem cursor {A : Type} (iter : Iter A) (a : A) (rest : List A)
    (h : iter.remaining=a::rest) :
    pointer (next iter).2=pointer iter+iter.allocation.layout.size := by
  unfold pointer
  rw [(moves iter a rest h).2.2.1,(moves iter a rest h).2.2.2]
  simp only [Nat.add_mul,Nat.one_mul,Nat.add_assoc]

theorem zst_cursor {A : Type} (iter : Iter A) (a : A) (rest : List A)
    (h : iter.remaining=a::rest) (zero : iter.allocation.layout.size=0) :
    pointer (next iter).2=pointer iter ∧
      (next iter).2.remaining.length+1=iter.remaining.length := by
  constructor
  · rw [cursor iter a rest h,zero,Nat.add_zero]
  · rw [(moves iter a rest h).2.1,h]
    rfl

theorem exhausted {A : Type} (iter : Iter A) (h : iter.remaining=[]) :
    next iter=(none,iter) ∧ release (next iter).2.allocation=release iter.allocation := by
  have hn : next iter=(none,iter) := by
    cases iter with
    | mk allocation consumed remaining fits =>
      dsimp only at h
      subst remaining
      rfl
  exact ⟨hn,by rw [hn]⟩

/-- On normal exhausted drop there is no element destructor and free uses the
ORIGINAL base, raw capacity and layout, even when the cursor is one-past-end. -/
def destructorOutcome {A : Type} : Outcome A → Outcome A
  | .fault (.panic p) => .fault (.abort p)
  | r => r

theorem exhausted_drop {S A : Type} (dropValue : A → Q S Unit)
    (free : Nat → Nat → Nat → Q S Unit) (iter : Iter A) (h : iter.remaining=[])
    (w : State S) :
    drop dropValue free iter w=⟨destructorOutcome (deallocate free iter.allocation w).outcome,
      (deallocate free iter.allocation w).state,(deallocate free iter.allocation w).events⟩ := by
  simp only [drop,h,dropValues,PV_V263_WorkerControl.finalize,PV_V263_World.lift,
    List.nil_append]
  cases hr : deallocate free iter.allocation w with
  | mk outcome state events =>
    cases outcome with
    | returned r => cases r <;> rfl
    | fault e => cases e <;> rfl
    | exhausted => rfl

#print axioms Iter
#print axioms intoIter
#print axioms pointer
#print axioms endPointer
#print axioms next
#print axioms deallocate
#print axioms dropValues
#print axioms drop
#print axioms moves
#print axioms cursor
#print axioms zst_cursor
#print axioms exhausted
#print axioms destructorOutcome
#print axioms exhausted_drop
end R1Z.PV_V263_OwnedIterator
