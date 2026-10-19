import AspisR1CuArrayGraph.Funs
import CuSavingsArrayGuard

/-! Exact one-step execution of the complete emitted initialization loop.
The counter bound proves unsafe-index/add preconditions. Callback failure and
divergence remain in the equation; callback success is not assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace AspisR1.CuSavingsArrayGraphStep
open Aeneas Aeneas.Std Result ControlFlow
open AspisR1CuArrayGraph

theorem guard_step {T : Type} (buffer : Slice (Option T)) (i next : Usize) (item : T)
    (hi : i.val < buffer.length) (hn : UScalar.add i 1#usize = .ok next) :
    core.array.Guard.push_unchecked {array_mut:=buffer,initialized:=i} item =
      .ok (({array_mut:=buffer.set i (some item),initialized:=next} : core.array.Guard T),
        fun replacement : core.array.Guard T => {array_mut:=replacement.array_mut,initialized:=i}) := by
  simp only [core.array.Guard.push_unchecked,
    core.slice.Slice.get_unchecked_mut,core.slice.index.Usize.index_mut,
    AspisR1CuArraySource.core.slice.Slice.get_unchecked_mut,
    CuSavingsArrayGuard.index_success buffer i hi,bind_tc_ok,
    core.mem.maybe_uninit.MaybeUninit.write,core.num.Usize.unchecked_add,
    AspisR1CuArraySource.core.mem.maybe_uninit.MaybeUninit.write,
    AspisR1CuArraySource.core.num.Usize.unchecked_add,hn]
  rfl

theorem body_step {T F : Type} (inst : Aeneas.Std.core.ops.function.FnMut F Usize T)
    (back : Slice (Option T) → Slice (Option T)) (state : F)
    (buffer : Slice (Option T)) (i : Usize) (hi : i.val < buffer.length) :
    ∃ next : Usize, next.val = i.val+1 ∧
      core.array.try_from_fn_erased_loop.body (CuSavingsTryGraphRuntime.neverTry T)
        inst back state buffer i = (do
          let (item,state1) ← inst.call_mut state i
          .ok (.cont (back,state1,buffer.set i (some item),next))) := by
  obtain ⟨next,hn,hv⟩ := CuSavingsArrayGuard.increment_success buffer i hi
  refine ⟨next,hv,?_⟩
  have hc : i < Slice.len buffer := by
    change i.val < (Slice.len buffer).val
    rw [Slice.len_val]
    exact hi
  simp only [core.array.try_from_fn_erased_loop.body,CuSavingsTryGraphRuntime.neverTry,
    if_pos hc]
  cases hcall : inst.call_mut state i with
  | fail e => rfl
  | div => rfl
  | ok pair =>
    rcases pair with ⟨item,state1⟩
    simp only [bind_tc_ok,CuSavingsTryGraphRuntime.DynamicTry.branch,
      CuSavingsTryGraph.neverTry,CuSavingsTryGraph.neverCore,
      AspisR1CuArraySource.core.ops.try_trait.NeverShortCircuit.Insts.CoreOpsTry_traitTry.branch,
      core.ops.control_flow.ControlFlow.Insts.CoreOpsTry_traitTry.branch,
      guard_step buffer i next item hi hn]
    rfl

theorem body_done {T F : Type} (inst : Aeneas.Std.core.ops.function.FnMut F Usize T)
    (back : Slice (Option T) → Slice (Option T)) (state : F)
    (buffer : Slice (Option T)) (i : Usize) (hi : buffer.length ≤ i.val) :
    core.array.try_from_fn_erased_loop.body (CuSavingsTryGraphRuntime.neverTry T)
        inst back state buffer i = .ok (.done (.Continue (),back buffer)) := by
  have hc : ¬ i < Slice.len buffer := by
    change ¬ i.val < (Slice.len buffer).val
    rw [Slice.len_val]
    omega
  simp only [core.array.try_from_fn_erased_loop.body,CuSavingsTryGraphRuntime.neverTry,
    if_neg hc,core.mem.forget,bind_tc_ok]

#print axioms guard_step
#print axioms body_step
#print axioms body_done
end AspisR1.CuSavingsArrayGraphStep
