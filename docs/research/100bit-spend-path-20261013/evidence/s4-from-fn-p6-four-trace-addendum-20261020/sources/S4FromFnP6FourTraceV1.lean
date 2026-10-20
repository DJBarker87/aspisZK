import S4FourDotsP6ArrayOperationV1

open Aeneas Aeneas.Std Result
set_option autoImplicit false

namespace AspisR1FromFnP6Generated
open AspisR1FastDotsCurrent

/-- Invert a successful generated FnMut model step without unfolding its
callback implementation. -/
theorem fnMutStep_success {T F : Type}
    (callback : core.ops.function.FnMut F Usize T)
    (state : F × Usize) (index : Nat) {value : T} {next : F × Usize}
    (h : fnMutStep callback state index = .ok (value, next)) :
    ∃ nextClosure nextIndex,
      callback.call_mut state.1 state.2 = .ok (value, nextClosure) ∧
      (state.2 + 1#usize : Result Usize) = .ok nextIndex ∧
      next = (nextClosure, nextIndex) := by
  unfold fnMutStep at h
  cases hcall : callback.call_mut state.1 state.2 with
  | fail e => simp [hcall] at h
  | div => simp [hcall] at h
  | ok pair =>
    rcases pair with ⟨actualValue, nextClosure⟩
    cases hadd : (state.2 + 1#usize : Result Usize) with
    | fail e => simp [hcall, hadd] at h
    | div => simp [hcall, hadd] at h
    | ok nextIndex =>
      simp only [hcall, bind_tc_ok, hadd, bind_tc_ok] at h
      have hp := Result.ok.inj h
      have hvalue : actualValue = value := (Prod.mk.inj hp).1
      have hnext : (nextClosure, nextIndex) = next := (Prod.mk.inj hp).2
      subst actualValue
      exact ⟨nextClosure, nextIndex, rfl, rfl, hnext.symm⟩

/-- A four-element P6 trace is exactly four ascending generated callback
steps; this exposes the calls used by the fixed-call candidate. -/
theorem statefulFromFnTrace_four_calls {T F : Type}
    (callback : core.ops.function.FnMut F Usize T)
    (initial : F × Usize) {values : List T} {final : F × Usize}
    (htrace : AspisR1FromFnP6.StatefulFromFnTrace (fnMutStep callback)
      4 0 initial values final) :
    ∃ v0 v1 v2 v3 s1 s2 s3 s4,
      values = [v0, v1, v2, v3] ∧
      fnMutStep callback initial 0 = .ok (v0, s1) ∧
      fnMutStep callback s1 1 = .ok (v1, s2) ∧
      fnMutStep callback s2 2 = .ok (v2, s3) ∧
      fnMutStep callback s3 3 = .ok (v3, s4) ∧
      final = s4 := by
  cases htrace with
  | @call _ _ _ state1 final value0 values0 h0 tail0 =>
    cases tail0 with
    | @call _ _ _ state2 final value1 values1 h1 tail1 =>
      cases tail1 with
      | @call _ _ _ state3 final value2 values2 h2 tail2 =>
        cases tail2 with
        | @call _ _ _ state4 final value3 values3 h3 tail3 =>
          cases tail3 with
          | done _ _ =>
            refine ⟨value0, value1, value2, value3, state1, state2, state3, final,
              ?_, h0, ?_, ?_, ?_, rfl⟩
            · rfl
            · simpa only [Nat.zero_add] using h1
            · simpa only [Nat.zero_add, Nat.add_assoc] using h2
            · simpa only [Nat.zero_add, Nat.add_assoc] using h3

/-- Specialize the four-step inversion to the actual generated S4 callback.
A successful N=4 P6 operation therefore contains four ordered successful
callback transitions on the same captured `(q1,g)` closure. -/
theorem fourDotsOuterGeneratedCallback_success_four_steps
    (ops : AspisR1FastDotsCurrent.FourDotsOps)
    (q1 : Aeneas.Std.Array Std.U8 608#usize)
    (g : Aeneas.Std.Array aspis_core.field.wide_exact.WideExact 29#usize)
    {values : Aeneas.Std.Array aspis_core.field.wide_exact.WideExact 4#usize}
    (h : (fourDotsOpsWithP6ArrayFromFn ops).arrayFromFn 4#usize
      (fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact
        (fourDotsOpsWithP6ArrayFromFn ops)) (q1, g) = .ok values) :
    ∃ v0 v1 v2 v3 s1 s2 s3 s4,
      values.val = [v0, v1, v2, v3] ∧
      fnMutStep
        (fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact
          (fourDotsOpsWithP6ArrayFromFn ops)) ((q1, g), 0#usize) 0 = .ok (v0, s1) ∧
      fnMutStep
        (fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact
          (fourDotsOpsWithP6ArrayFromFn ops)) s1 1 = .ok (v1, s2) ∧
      fnMutStep
        (fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact
          (fourDotsOpsWithP6ArrayFromFn ops)) s2 2 = .ok (v2, s3) ∧
      fnMutStep
        (fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact
          (fourDotsOpsWithP6ArrayFromFn ops)) s3 3 = .ok (v3, s4) := by
  obtain ⟨final, htrace⟩ := fourDotsOuterGeneratedCallback_success_trace ops q1 g h
  obtain ⟨v0, v1, v2, v3, s1, s2, s3, s4, hvalues, h0, h1, h2, h3, _⟩ :=
    statefulFromFnTrace_four_calls
      (fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact
        (fourDotsOpsWithP6ArrayFromFn ops)) ((q1, g), 0#usize) htrace
  exact ⟨v0, v1, v2, v3, s1, s2, s3, s4, hvalues, h0, h1, h2, h3⟩

#print axioms fnMutStep_success
#print axioms statefulFromFnTrace_four_calls
#print axioms fourDotsOuterGeneratedCallback_success_four_steps

end AspisR1FromFnP6Generated
