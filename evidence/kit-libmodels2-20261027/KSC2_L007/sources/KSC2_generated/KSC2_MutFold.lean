import KSC2_MutCounterexamples
open Aeneas Aeneas.Std Result ControlFlow
namespace KSC2

def mutatingFoldValue : core.ops.function.FnMut Unit (Nat × Nat) Nat :=
  { FnOnceInst := {call_once := fun _ p => ok (p.1+p.2+10)}
    call_mut := fun _ p => ok (p.1+p.2+10,()) }
abbrev FoldState := Nat × core.slice.iter.IterMut Nat × Unit
def foldStep (s : FoldState) : Result (ControlFlow FoldState FoldState) := do
  let (item,next,_) ← core.slice.iter.IteratorIterMut.next s.2.1
  match item with
  | none => ok (done (s.1,next,s.2.2))
  | some value =>
    let (acc,c) ← mutatingFoldValue.call_mut s.2.2 (s.1,value)
    ok (cont (acc,next,c))

theorem fold_step0 : foldStep (0,⟨two,0⟩,()) = ok (cont (11,⟨two,1⟩,())) := rfl
theorem fold_step1 : foldStep (11,⟨two,1⟩,()) = ok (cont (23,⟨two,2⟩,())) := rfl
theorem fold_step2 : foldStep (23,⟨two,2⟩,()) = ok (done (23,⟨two,2⟩,())) := rfl

theorem fold_loop : loop foldStep (0,⟨two,0⟩,()) = ok (23,⟨two,2⟩,()) := by
  rw [loop.eq_def,fold_step0]
  rw [loop.eq_def,fold_step1]
  rw [loop.eq_def,fold_step2]

theorem mutable_fold_loses_writeback :
    (do let (n,s) ← KSA_Isolated.core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT.fold mutatingFoldValue ⟨two,0⟩ 0 ()
        ok (n,s.slice.val) : Result (Nat × List Nat)) = ok (23,[1,2]) := by
  unfold KSA_Isolated.core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT.fold
  change (do let r ← loop foldStep (0,⟨two,0⟩,()); ok (r.1,r.2.1.slice.val)) = _
  rw [fold_loop]
  rfl
#print axioms fold_step0
#print axioms fold_step1
#print axioms fold_step2
#print axioms fold_loop
#print axioms mutable_fold_loses_writeback
end KSC2
