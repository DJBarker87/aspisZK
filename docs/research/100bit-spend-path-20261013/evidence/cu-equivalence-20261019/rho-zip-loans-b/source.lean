import Aeneas

/-! Package the existing mutable-iterator handback as the yielded loan value.
The zip operation itself is the unchanged generic runtime Zip.next, rather
than a new assumed mutable Zip primitive. No initializer theorem is claimed.
-/
set_option autoImplicit false
namespace AspisR1.CuSavingsZipLoans
open Aeneas Aeneas.Std Result
abbrev MutIter (T : Type) := core.slice.iter.IterMut T
abbrev ReadIter (T : Type) := core.slice.iter.Iter T

structure Loan (T : Type) where
  value : T
  write : MutIter T → T → MutIter T

def loanNext {T : Type} (iter : MutIter T) : Result (Option (Loan T) × MutIter T) := do
  let (item,next,back) ← core.slice.iter.IteratorIterMut.next iter
  match item with
  | none => .ok (none,next)
  | some value => .ok (some ⟨value,fun state replacement => back state (some replacement)⟩,next)

def loanIterator (T : Type) : core.iter.traits.iterator.Iterator (MutIter T) (Loan T) :=
  {next:=loanNext}

abbrev Zip (T U : Type) := core.iter.adapters.zip.Zip (MutIter T) (ReadIter U)

def zipNext {T U : Type} (zip : Zip T U) : Result (Option (Loan T × U) × Zip T U) :=
  core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
    (loanIterator T) (core.iter.traits.iterator.IteratorSliceIter U) zip

theorem next_write {T : Type} (iter : MutIter T)
    (hi : iter.i < iter.slice.val.length) :
    loanNext iter = .ok
      (some ⟨iter.slice.val[iter.i]'hi,
        fun state replacement => {state with slice:=state.slice.setAtNat iter.i replacement}⟩,
       {iter with i:=iter.i+1}) := by
  have hlen : iter.slice.len.val = iter.slice.val.length := by
    simpa only [Slice.length] using Slice.len_val iter.slice
  have hactive : iter.i < iter.slice.len := by simpa only [hlen] using hi
  simp only [loanNext,core.slice.iter.IteratorIterMut.next,dif_pos hactive,bind_tc_ok]
  rfl

theorem next_done {T : Type} (iter : MutIter T)
    (hi : iter.slice.val.length ≤ iter.i) : loanNext iter = .ok (none,iter) := by
  have hlen : iter.slice.len.val = iter.slice.val.length := by
    simpa only [Slice.length] using Slice.len_val iter.slice
  have hstop : ¬ iter.i < iter.slice.len := by simpa only [hlen] using Nat.not_lt.mpr hi
  simp only [loanNext,core.slice.iter.IteratorIterMut.next,dif_neg hstop,bind_tc_ok]
  rfl

#print axioms next_write
#print axioms next_done
#print axioms zipNext
end AspisR1.CuSavingsZipLoans
