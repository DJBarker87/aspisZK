import KSC2_Simple
open Aeneas Aeneas.Std Result ControlFlow
namespace KSC2

def singleton : Slice Nat := ⟨[7], by scalar_tac⟩
def two : Slice Nat := ⟨[1,2], by scalar_tac⟩
def exhausted : core.slice.iter.IterMut Nat := ⟨singleton,1⟩

theorem mutable_back_repeats_consumed :
    (do let (item,_,_) ← KSA_Isolated.core.slice.iter.IterMut.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorMutT.next_back exhausted
        ok item : Result (Option Nat)) = ok (some 7) := by rfl

theorem exhausted_has_no_remaining : exhausted.slice.val.drop exhausted.i = [] := rfl

-- A predicate over a mutable Rust item needs a write-back of that item.
-- The kit's FnMut T Bool field cannot return such a value.
def truePredicate : core.ops.function.FnMut Unit Nat Bool :=
  { FnOnceInst := {call_once := fun _ _ => ok true}
    call_mut := fun _ _ => ok (true,()) }
def falsePredicate : core.ops.function.FnMut Unit Nat Bool :=
  { FnOnceInst := {call_once := fun _ _ => ok false}
    call_mut := fun _ _ => ok (false,()) }

theorem mutable_any_loses_writeback :
    (do let (b,s,restore) ← KSA_Isolated.core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT.any truePredicate ⟨two,0⟩ ()
        ok (b,(restore s).slice.val) : Result (Bool × List Nat)) = ok (true,[1,2]) := by
  unfold KSA_Isolated.core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT.any
    KSA_Isolated.core.iter.traits.iterator.Iterator.any.default
  rw [loop.eq_def]
  rfl

theorem mutable_all_loses_writeback :
    (do let (b,s,restore) ← KSA_Isolated.core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT.all falsePredicate ⟨two,0⟩ ()
        ok (b,(restore s).slice.val) : Result (Bool × List Nat)) = ok (false,[1,2]) := by
  unfold KSA_Isolated.core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT.all
    KSA_Isolated.core.iter.traits.iterator.Iterator.all.default
    KSA_Isolated.XRn_Join_iterator KSA_Isolated.XRn_Join_next
  rw [loop.eq_def]
  rfl

-- The most direct native comparison uses a callback which reads only, so no
-- callback-encoding question can mask the crossed-cursor counterexample.
theorem mutable_back_disagrees_with_empty_spec :
    (do let (item,_,_) ← KSA_Isolated.core.slice.iter.IterMut.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorMutT.next_back exhausted
        ok item : Result (Option Nat)) ≠ ok none := by
  rw [mutable_back_repeats_consumed]
  intro h
  cases h

def mutatingFoldValue : core.ops.function.FnMut Unit (Nat × Nat) Nat :=
  { FnOnceInst := {call_once := fun _ p => ok (p.1+p.2+10)}
    call_mut := fun _ p => ok (p.1+p.2+10,()) }

theorem mutable_fold_loses_writeback :
    (do let (n,s) ← KSA_Isolated.core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT.fold mutatingFoldValue ⟨two,0⟩ 0 ()
        ok (n,s.slice.val) : Result (Nat × List Nat)) = ok (23,[1,2]) := by
  unfold KSA_Isolated.core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT.fold
  rw [loop.eq_def]
  simp only [core.slice.iter.IteratorIterMut.next, two, Slice.len, List.length_cons,
    List.length_nil, Nat.reduceAdd, Nat.reduceLT, ↓reduceDIte, bind_tc_ok,
    mutatingFoldValue]
  rw [loop.eq_def]
  simp only [core.slice.iter.IteratorIterMut.next, two, Slice.len, List.length_cons,
    List.length_nil, Nat.reduceAdd, Nat.reduceLT, ↓reduceDIte, bind_tc_ok,
    mutatingFoldValue]
  rw [loop.eq_def]
  rfl

#print axioms mutable_fold_loses_writeback
#print axioms mutable_back_repeats_consumed
#print axioms exhausted_has_no_remaining
#print axioms mutable_any_loses_writeback
#print axioms mutable_all_loses_writeback
#print axioms mutable_back_disagrees_with_empty_spec
end KSC2
