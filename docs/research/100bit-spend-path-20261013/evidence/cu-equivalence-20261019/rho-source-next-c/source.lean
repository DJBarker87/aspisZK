import AspisR1CuRhoSource.Runtime

/-! Consume the source/model next comparison as a success-and-handback
contract. The backward counter need not agree; the inner iterator must agree
after the actual replacement supplied by finish. -/
set_option autoImplicit false
namespace AspisR1.CuSavingsRhoSourceNext
open Aeneas Aeneas.Std Result
open CuSavingsIteratorBridge
variable {T : Type}

abbrev selectedNext := @AspisR1CuRhoSource.core.iter.adapters.enumerate.IteratorEnumerate.next T
  (AspisR1CuRho.core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT T)

def runtimeView (input : Enum T) (replacement : Usize × T) :
    Result (Option (Usize × T) × Enum T × (Enum T → Iter T)) := do
  let (value,state,back) ← selectedNext input
  .ok (value,state,fun out => (back out (some replacement)).iter)

theorem runtime_view_eq (input : Enum T) (replacement : Usize × T) :
    runtimeView input replacement = modelView input replacement := by
  unfold runtimeView selectedNext AspisR1CuRhoSource.core.iter.adapters.enumerate.IteratorEnumerate.next
  change (do
    let triple ← (do
      let (value,state,back) ← CuSavingsIteratorSource.next (fromStd input)
      Result.ok (value,toStd state,fun (out : Enum T) (item : Option (Usize × T)) =>
        toStd (back (fromStd out) item)))
    Result.ok (triple.1,triple.2.1,fun out : Enum T => (triple.2.2 out (some replacement)).iter)) = _
  simp only [bind_assoc_eq,bind_tc_ok]
  exact source_model_write_eq input replacement

theorem from_model_success (input : Enum T) (replacement : Usize × T)
    (value : Option (Usize × T)) (state : Enum T)
    (modelBack : Enum T → Option (Usize × T) → Enum T)
    (hm : modelNext input = .ok (value,state,modelBack)) :
    ∃ sourceBack : Enum T → Option (Usize × T) → Enum T,
      selectedNext input = .ok (value,state,sourceBack) ∧
      ∀ out, (sourceBack out (some replacement)).iter =
        (modelBack out (some replacement)).iter := by
  have hv := runtime_view_eq input replacement
  simp only [modelView,hm,bind_tc_ok] at hv
  cases hs : selectedNext input with
  | fail e => simp only [runtimeView,hs,bind_tc_fail] at hv;cases hv
  | div => simp only [runtimeView,hs,bind_tc_div] at hv;cases hv
  | ok triple =>
    rcases triple with ⟨sourceValue,sourceState,sourceBack⟩
    simp only [runtimeView,hs,bind_tc_ok] at hv
    change Result.ok (sourceValue,sourceState,
      fun out : Enum T => (sourceBack out (some replacement)).iter) =
      Result.ok (value,state,fun out : Enum T => (modelBack out (some replacement)).iter) at hv
    have hp := Result.ok.inj hv
    have ho := congrArg Prod.fst hp
    have ht := congrArg (fun pair => pair.2.1) hp
    have hb := congrArg (fun pair => pair.2.2) hp
    refine ⟨sourceBack,?_,?_⟩
    · simp only [ho,ht]
    · intro out
      exact congrFun hb out

theorem next_done (input : Enum T) (hend : input.iter.i = input.iter.slice.val.length) :
    selectedNext input = .ok (none,input,fun out _ => {input with iter := out.iter}) := by
  have hlen : input.iter.slice.len.val = input.iter.slice.val.length := by
    simpa only [Slice.length] using Slice.len_val input.iter.slice
  have hn : Aeneas.Std.core.slice.iter.IteratorIterMut.next input.iter =
      .ok (none,input.iter,fun out _ => out) := by
    unfold Aeneas.Std.core.slice.iter.IteratorIterMut.next
    split
    · rename_i hi;exact False.elim (by omega)
    · rfl
  unfold selectedNext AspisR1CuRhoSource.core.iter.adapters.enumerate.IteratorEnumerate.next
  rw [CuSavingsIteratorSource.source_none (fromStd input) input.iter (fun out _ => out) hn]
  rfl

#print axioms runtime_view_eq
#print axioms from_model_success
#print axioms next_done
end AspisR1.CuSavingsRhoSourceNext
