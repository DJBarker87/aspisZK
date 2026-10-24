import AspisR1S9ProductionPairCutV1.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open AspisR1S9ProductionPairCutV1
namespace AspisR1S9ActualPairSourceScalarTraceV1
abbrev W := aspis_core.field.wide_exact.WideExact
abbrev Q := aspis_core.field.QM31

theorem source_scalar_success_trace (f : Array Q 4#usize) (p : Array W 4#usize) (out : W)
    (h : weights.Weights.scalar_factor f p = .ok out) :
    ∃ acc,
      core.iter.traits.iterator.Iterator.fold.default
        (Aeneas.Std.core.iter.traits.iterator.IteratorRange Aeneas.Std.core.iter.range.StepUsize)
        weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact
        ({start:=0#usize,«end»:=4#usize} : Aeneas.Std.core.ops.range.Range Usize)
        aspis_core.field.wide_exact.WideExact.ZERO (p,f) = .ok acc ∧
      aspis_core.field.wide_exact.WideExact.mul_m31 acc weights.QUARTER = .ok out := by
  unfold weights.Weights.scalar_factor at h
  cases hf : core.iter.traits.iterator.Iterator.fold.default
      (Aeneas.Std.core.iter.traits.iterator.IteratorRange Aeneas.Std.core.iter.range.StepUsize)
      weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact
      ({start:=0#usize,«end»:=4#usize} : Aeneas.Std.core.ops.range.Range Usize)
      aspis_core.field.wide_exact.WideExact.ZERO (p,f) with
  | fail e => simp only [hf,bind_tc_fail] at h; cases h
  | div => simp only [hf,bind_tc_div] at h; cases h
  | ok acc =>
    simp only [hf,bind_tc_ok] at h
    exact ⟨acc,rfl,h⟩
#print axioms source_scalar_success_trace
end AspisR1S9ActualPairSourceScalarTraceV1
