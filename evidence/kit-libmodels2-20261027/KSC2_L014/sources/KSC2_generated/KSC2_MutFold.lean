import KSC2_MutCounterexamples
open Aeneas Aeneas.Std Result ControlFlow
namespace KSC2

def mutatingFoldValue : core.ops.function.FnMut Unit (Nat × Nat) Nat :=
  { FnOnceInst := {call_once := fun _ p => ok (p.1+p.2+10)}
    call_mut := fun _ p => ok (p.1+p.2+10,()) }
abbrev FoldState := Nat × core.slice.iter.IterMut Nat × Unit
def foldStep : FoldState → Result (ControlFlow FoldState FoldState) :=
  fun (acc,state,c) => do
    let (item,next,_) ← core.slice.iter.IteratorIterMut.next state
    match item with
    | none => ok (done (acc,next,c))
    | some value =>
      let (acc1,c1) ← mutatingFoldValue.call_mut c (acc,value)
      ok (cont (acc1,next,c1))

theorem fold_step0 : foldStep (0,⟨two,0⟩,()) = ok (cont (11,⟨two,1⟩,())) := rfl
theorem fold_step1 : foldStep (11,⟨two,1⟩,()) = ok (cont (23,⟨two,2⟩,())) := rfl
theorem fold_step2 : foldStep (23,⟨two,2⟩,()) = ok (done (23,⟨two,2⟩,())) := rfl

theorem fold_loop : loop foldStep (0,⟨two,0⟩,()) = ok (23,⟨two,2⟩,()) := by
  rw [loop.eq_def,fold_step0]
  change loop foldStep (11,⟨two,1⟩,()) = _
  rw [loop.eq_def,fold_step1]
  change loop foldStep (23,⟨two,2⟩,()) = _
  rw [loop.eq_def,fold_step2]

theorem fold_body_eq :
    (fun x : FoldState => do
      let (item,stateNext,_) ← core.slice.iter.IteratorIterMut.next x.2.1
      match item with
      | none => ok (done (x.1,stateNext,x.2.2))
      | some value => do
        let (accNext,closureNext) ← mutatingFoldValue.call_mut x.2.2 (x.1,value)
        ok (cont (accNext,stateNext,closureNext))) = foldStep := by
  funext x
  rcases x with ⟨acc,state,c⟩
  rfl

theorem mutable_fold_result :
    KSA_Isolated.core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT.fold
      mutatingFoldValue (⟨two,0⟩ : core.slice.iter.IterMut Nat) 0 () =
      ok (23,(⟨two,2⟩ : core.slice.iter.IterMut Nat)) := by
  unfold KSA_Isolated.core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT.fold
  rw [fold_loop]
  rfl

theorem mutable_fold_loses_writeback :
    (do let (n,s) ← KSA_Isolated.core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT.fold mutatingFoldValue ⟨two,0⟩ 0 ()
        ok (n,s.slice.val) : Result (Nat × List Nat)) = ok (23,[1,2]) := by
  rw [mutable_fold_result]
  rfl
#print axioms mutable_fold_result
#print axioms fold_body_eq
#print axioms fold_step0
#print axioms fold_step1
#print axioms fold_step2
#print axioms fold_loop
#print axioms mutable_fold_loses_writeback
end KSC2
