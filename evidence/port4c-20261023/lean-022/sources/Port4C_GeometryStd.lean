import Port3_GeometryStage
import Port3_BatchStd
import MultiproofConeVecLaws

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4C_GeometryStd
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2
open Port3_NativeGeometryBody
variable {CoreError : Type}
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def mapError {T E F O : Type} (f : core.ops.function.FnOnce O E F)
    (r : core.result.Result T E) (o : O) : Result (core.result.Result T F) := do
  match r with
  | .Ok x => ok (.Ok x)
  | .Err e => let e1 ← f.call_once o e; ok (.Err e1)

def install (ops : Ops CoreError) : Ops CoreError :=
  {ops with
    op2 := mapError
    op3 := (fun pred it f =>
    Port3_BatchStd.anyDefault (core.iter.traits.iterator.IteratorSliceIter _) pred it f)

    op4 := fun _ v => ok v.val.isEmpty

    op5 := fun x y => ok (decide (x=y))
    op6 := ok (0#u32)}

/-- The current geometry zero-test closure uses exactly raw M31 equality. -/
theorem zero_closure (ops : Ops CoreError) (x : U32) :
    verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool.call_mut
      (install ops) () x=ok (decide (x=0#u32),()) := rfl

/-- Clone/extend retains all five gathered operands in order. -/
theorem clone_m31 (s : Slice U32) :
    Slice.clone core.marker.CopyU32.cloneInst.clone s=ok s := by
  obtain ⟨out,ho,hv⟩ := WP.spec_imp_exists
    (Slice.clone_spec (clone:=core.marker.CopyU32.cloneInst.clone) (s:=s) (by intros; rfl))
  simpa only [←hv] using ho

theorem extend_fields (flat out : alloc.vec.Vec U32) (s : Slice U32)
    (h : alloc.vec.Vec.extend_from_slice core.marker.CopyU32.cloneInst flat s=ok out) :
    out.val=flat.val++s.val := by
  unfold alloc.vec.Vec.extend_from_slice at h
  split at h
  · split at h
    · rename_i cloned hc
      have same := Result.ok.inj (hc.symm.trans (clone_m31 s))
      subst cloned
      cases Result.ok.inj h
      rfl
    · rename_i e hc
      have impossible := clone_m31 s
      rw [hc] at impossible
      cases impossible
    · rename_i hc
      have impossible := clone_m31 s
      rw [hc] at impossible
      cases impossible
  · cases h

private theorem any_step {T : Type} (P : T → Bool)
    (pred : core.ops.function.FnMut Unit T Bool)
    (callback : ∀ x, pred.call_mut () x=ok (P x,()))
    (it it1 : core.slice.iter.Iter T) (x : T)
    (nextRun : core.slice.iter.IteratorSliceIter.next it=ok (some x,it1)) :
    Port3_BatchStd.anyDefault (core.iter.traits.iterator.IteratorSliceIter T) pred it () =
      if P x then ok (true,it1) else
        Port3_BatchStd.anyDefault (core.iter.traits.iterator.IteratorSliceIter T) pred it1 () := by
  unfold Port3_BatchStd.anyDefault
  rw [Aeneas.Std.loop.eq_def]
  simp only [Port3_BatchStd.anyBody,core.iter.traits.iterator.IteratorSliceIter,
    nextRun,bind_tc_ok,callback]
  cases hp : P x <;> simp [hp]

/-- Pure std Iterator::any, with the actual FnMut callback. Successful false
means every visited element's predicate is false; no finite-field enumeration. -/
theorem any_false {T : Type} (P : T → Bool)
    (pred : core.ops.function.FnMut Unit T Bool)
    (callback : ∀ x, pred.call_mut () x=ok (P x,()))
    (it after : core.slice.iter.Iter T) (fuel : Nat)
    (remaining : it.i+fuel=it.slice.val.length)
    (h : Port3_BatchStd.anyDefault (core.iter.traits.iterator.IteratorSliceIter T)
      pred it ()=ok (false,after)) :
    ∀ j, it.i≤j → (hj : j< it.slice.val.length) → P it.slice.val[j]=false := by
  induction fuel generalizing it after with
  | zero => intro j lo hi; omega
  | succ fuel ih =>
    have active : it.i < it.slice.val.length := by omega
    have nextRun : core.slice.iter.IteratorSliceIter.next it =
        ok (some it.slice.val[it.i],{it with i:=it.i+1}) := by
      unfold core.slice.iter.IteratorSliceIter.next
      split
      · rfl
      · rename_i bad
        exact False.elim (bad active)
    rw [any_step P pred callback it {it with i:=it.i+1} _ nextRun] at h
    split at h
    · cases h
    · rename_i notTrue
      have hp : P it.slice.val[it.i]=false := Bool.eq_false_iff.mpr notTrue
      have rest := ih {it with i:=it.i+1} after (by simp; omega) h
      intro j lo hi
      by_cases eq : j=it.i
      · subst j; exact hp
      · exact rest j (by simp; omega) hi

theorem zero_test_false (ops : Ops CoreError) (values : Slice U32)
    (after : core.slice.iter.Iter U32)
    (h : (install ops).op3
      (verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool (install ops))
      ⟨values,0⟩ ()=ok (false,after)) :
    ∀ j (hj : j< values.val.length), values.val[j]≠0#u32 := by
  have all := any_false (fun x : U32 => decide (x=0#u32))
    (verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool (install ops))
    (zero_closure ops) ⟨values,0⟩ after values.val.length (by simp) h
  intro j hj
  have hf := all j (Nat.zero_le _) hj
  exact of_decide_eq_false hf

#print axioms zero_closure
#print axioms clone_m31
#print axioms extend_fields
#print axioms any_false
#print axioms zero_test_false
end AspisR1.Port4C_GeometryStd
end
