import AspisR318BatchPrefixRaw
import AspisV8R19.R317SliceLastExecution
import AspisV8R19.R250PrivateBaseExecution

/-! Exact forward-prefix body execution in the pinned extraction library.
Local read and capacity premises are not yet established for the source caller.
The all-word active-body theorem retains every multiplication/push failure. -/
set_option autoImplicit false
namespace AspisV8R19.R319BatchPrefixStepExecution
open Aeneas Aeneas.Std Result ControlFlow WP
open AspisV8R15.ExactTowerBase
open ComplexBaseExecution (encodeBase)
open AspisR318BatchPrefixRaw.circle_norm.joined_inverse.line_norm.r110_norm
noncomputable section

abbrev PrefixIter := core.slice.iter.Iter U32

theorem next_done (iter : PrefixIter) (hstop : iter.slice.val.length ≤ iter.i) :
    core.slice.iter.IteratorSliceIter.next iter = .ok (none, iter) := by
  simp only [core.slice.iter.IteratorSliceIter.next, Slice.len_val]
  simp only [show ¬ iter.i < iter.slice.val.length from by omega, ↓reduceDIte]

theorem next_step (iter : PrefixIter) (hstep : iter.i < iter.slice.val.length) :
    core.slice.iter.IteratorSliceIter.next iter =
      .ok (some iter.slice.val[iter.i], {iter with i := iter.i + 1}) := by
  simp only [core.slice.iter.IteratorSliceIter.next, Slice.len_val, hstep,
    ↓reduceDIte]
  rfl

theorem body0_done (iter : PrefixIter) (px : alloc.vec.Vec U32)
    (hstop : iter.slice.val.length ≤ iter.i) :
    batch_loop0.body iter px = .ok (.done px) := by
  simp only [batch_loop0.body, next_done iter hstop, bind_tc_ok]

theorem body0_active (iter : PrefixIter) (px : alloc.vec.Vec U32)
    (hstep : iter.i < iter.slice.val.length) :
    batch_loop0.body iter px = (do
      let p ← core.option.Option.unwrap px.val.getLast?
      let b ← AspisR249R110Raw.circle_norm.joined_inverse.line_norm.r110_norm.B.mul
        p iter.slice.val[iter.i]
      let px1 ← alloc.vec.Vec.push px b
      .ok (.cont ({iter with i := iter.i + 1}, px1))) := by
  simp only [batch_loop0.body, next_step iter hstep, bind_tc_ok,
    R317SliceLastExecution.last_complete, alloc.vec.Vec.deref]

theorem body0_empty_prefix (iter : PrefixIter) (px : alloc.vec.Vec U32)
    (hstep : iter.i < iter.slice.val.length) (hempty : px.val = []) :
    batch_loop0.body iter px = .fail .panic := by
  rw [body0_active iter px hstep]
  simp only [hempty, List.getLast?_nil, core.option.Option.unwrap, Result.ofOption, bind_tc_fail]

theorem body0_step (iter : PrefixIter) (px : alloc.vec.Vec U32)
    (x p : M31Exact) (hstep : iter.i < iter.slice.val.length)
    (hx : iter.slice.val[iter.i] = encodeBase x)
    (hp : px.val.getLast? = some (encodeBase p))
    (hcap : px.val.length < Usize.max) :
    ∃ px1 : alloc.vec.Vec U32,
      px1.val = px.val ++ [encodeBase (p*x)] ∧
      batch_loop0.body iter px = .ok (.cont ({iter with i := iter.i + 1}, px1)) := by
  obtain ⟨px1, hpush, hval⟩ := spec_imp_exists
    (alloc.vec.Vec.push_spec px (encodeBase (p*x)) hcap)
  refine ⟨px1, hval, ?_⟩
  simp only [body0_active iter px hstep, hp, hx, core.option.Option.unwrap, Result.ofOption,
    bind_tc_ok, R250PrivateBaseExecution.mul_encoded, hpush]

theorem body1_eq_body0 (iter : PrefixIter) (py : alloc.vec.Vec U32) :
    batch_loop1.body iter py = batch_loop0.body iter py := by rfl

#print axioms next_done
#print axioms next_step
#print axioms body0_done
#print axioms body0_active
#print axioms body0_empty_prefix
#print axioms body0_step
#print axioms body1_eq_body0
end
end AspisV8R19.R319BatchPrefixStepExecution
