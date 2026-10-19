import CuSavingsDotsBase

/-! The complete emitted batch loop only invokes the base loop with end at
most 26. This bound follows from the actual scalar min result. No batch-loop
termination or successful arithmetic premise is needed for the comparison. -/
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace AspisR1.CuSavingsDotsBatches
open Aeneas Aeneas.Std Result ControlFlow AspisR1CuDots
open CuSavingsPrefix

theorem min_bound (x y out : Usize) (h : core.cmp.min core.cmp.OrdUsize x y = .ok out) :
    out.val ≤ y.val := by
  change .ok (if x < y then x else y) = .ok out at h
  by_cases hx : x < y
  · rw [if_pos hx] at h
    cases h
    have hv : x.val < y.val := by simpa only [UScalar.lt_equiv] using hx
    omega
  · rw [if_neg hx] at h
    cases h
    exact Nat.le_refl _

variable [Arithmetic]
local notation "batchBody" =>
  old_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0.body
local notation "batchLoop" =>
  old_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0

theorem body_eq (bytes : Slice U8) (h : 608 ≤ bytes.val.length)
    (gamma : Array field.wide_exact.WideExact 29#usize) (slot : Usize)
    (iter : core.iter.adapters.step_by.StepBy (core.ops.range.Range Usize))
    (limbs : Array U64 8#usize) (hs : slot.val < 4) :
    batchBody (prefixArray bytes h).to_slice gamma slot iter limbs =
      batchBody bytes gamma slot iter limbs := by
  unfold old_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0.body
  apply (bind_eq_iff _ _ _).mpr
  intro result hr
  rcases result with ⟨opt,next⟩
  cases opt with
  | none => rfl
  | some start =>
    apply (bind_eq_iff _ _ _).mpr
    intro i hi
    apply (bind_eq_iff _ _ _).mpr
    intro stop hstop
    have hb := min_bound i 26#usize stop hstop
    have h26 : (26#usize).val = 26 := by scalar_tac
    rw [CuSavingsDotsBase.source_eq bytes h gamma slot {start,«end» := stop}
      (Array.repeat 8#usize 0#u64) hs (by simpa only [h26] using hb)]

theorem source_eq (bytes : Slice U8) (h : 608 ≤ bytes.val.length)
    (gamma : Array field.wide_exact.WideExact 29#usize) (slot : Usize)
    (iter : core.iter.adapters.step_by.StepBy (core.ops.range.Range Usize))
    (limbs : Array U64 8#usize) (hs : slot.val < 4) :
    batchLoop iter (prefixArray bytes h).to_slice gamma slot limbs =
      batchLoop iter bytes gamma slot limbs := by
  have bodies :
      (fun (it,acc) => batchBody (prefixArray bytes h).to_slice gamma slot it acc) =
        (fun (it,acc) => batchBody bytes gamma slot it acc) := by
    funext state
    rcases state with ⟨it,acc⟩
    exact body_eq bytes h gamma slot it acc hs
  unfold old_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0
  exact congrArg (fun body => loop body (iter,limbs)) bodies

#print axioms min_bound
#print axioms body_eq
#print axioms source_eq
end AspisR1.CuSavingsDotsBatches
