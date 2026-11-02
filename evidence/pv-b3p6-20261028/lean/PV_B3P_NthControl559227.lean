import PV_B3P_NthGuard559227
namespace PV_B3P_NthControl559227
open Aeneas Aeneas.Std core.ops.range PV_B3P_NthGuard559227
set_option autoImplicit false
/-- A source-control interpretation of the default std helper. The diagnostic
message and its handler remain arbitrary; no literal's elaboration is trusted.
This is not an equality theorem about the quarantined emitted function. -/
def control (message : Str) (handler : Str → Result Never)
    (r : Range Usize) (n : Usize) : Result (Option Usize × Range Usize) := do
  let t ← core.iter.range.StepUsize.cloneInst.clone r.start
  let candidate ← core.iter.range.StepUsize.forward_checked t n
  match candidate with
  | none => do
      let t1 ← core.iter.range.StepUsize.cloneInst.clone r.end
      .ok (none,{r with start := t1})
  | some item => do
      let b ← core.iter.range.StepUsize.partialOrdInst.lt item r.end
      if b then do
        let t1 ← core.iter.range.StepUsize.cloneInst.clone item
        let next ← core.iter.range.StepUsize.forward_checked t1 1#usize
        match next with
        | none => do
            let _ ← handler message
            .fail .panic
        | some value => .ok (some item,{r with start := value})
      else do
        let t1 ← core.iter.range.StepUsize.cloneInst.clone r.end
        .ok (none,{r with start := t1})

def source (r : Range Usize) (n : Usize) : Result (Option Usize × Range Usize) := do
  let candidate ← core.iter.range.StepUsize.forward_checked r.start n
  match candidate with
  | none => .ok (none,{r with start := r.end})
  | some item =>
      if item.val < r.end.val then
        .ok (some item,{r with start := Usize.wrapping_add item 1#usize})
      else .ok (none,{r with start := r.end})

theorem clone_value (v : Usize) :
    core.iter.range.StepUsize.cloneInst.clone v = .ok v := rfl

theorem less_value (v w : Usize) :
    core.iter.range.StepUsize.partialOrdInst.lt v w = .ok (decide (v.val < w.val)) := rfl

theorem increment_wrap (item end_ : Usize) (guard : item.val < end_.val) :
    core.iter.range.StepUsize.forward_checked item 1#usize =
      .ok (some (Usize.wrapping_add item 1#usize)) := by
  obtain ⟨next,run,value⟩ := increment_some item end_ guard
  have wrap : (Usize.wrapping_add item 1#usize).val = item.val+1 := by
    rw [Usize.wrapping_add_val_eq]
    exact Nat.mod_eq_of_lt (PV_B3Q_RangeActual.increment_safe ⟨item,end_⟩ guard)
  have same : next = Usize.wrapping_add item 1#usize :=
    UScalar.eq_of_val_eq (value.trans wrap.symm)
  exact same ▸ run

/-- Full Result equality for all ranges and skips, including exhausted and
reversed ranges. The panic branch is excluded, not modeled as always-Ok. -/
theorem source_binding (message : Str) (handler : Str → Result Never)
    (r : Range Usize) (n : Usize) : source r n = control message handler r n := by
  unfold source control
  rw [clone_value,bind_tc_ok]
  apply congrArg (Aeneas.Std.bind _)
  funext candidate
  cases candidate with
  | none => rw [clone_value,bind_tc_ok]
  | some item =>
      simp only [less_value,bind_tc_ok]
      by_cases guard : item.val < r.end.val
      · simp only [guard,decide_true,↓reduceIte]
        rw [clone_value,bind_tc_ok,increment_wrap item r.end guard,bind_tc_ok]
      · simp only [guard,decide_false,↓reduceIte]
        rw [clone_value,bind_tc_ok]

theorem formatting_independent (message1 message2 : Str)
    (first second : Str → Result Never) (r : Range Usize) (n : Usize) :
    control message1 first r n = control message2 second r n :=
  (source_binding message1 first r n).symm.trans (source_binding message2 second r n)

#print axioms clone_value
#print axioms less_value
#print axioms increment_wrap
#print axioms source_binding
#print axioms formatting_independent
end PV_B3P_NthControl559227
