import S4FromFnP6GeneratedInterface
import AspisR1FastDotsCurrent.FunsOpsV4

open Aeneas Aeneas.Std Result AspisR1FastDotsCurrent
set_option autoImplicit false

namespace AspisR1FromFnP6Generated

/-- Array-returning operation adapter with the generated `FnMut` ABI. -/
def arrayFromFnP6 {T F : Type} (N : Usize)
    (callback : core.ops.function.FnMut F Usize T) (initial : F) :
    Result (Aeneas.Std.Array T N) := do
  let (values, _final) ← core.array.from_fn_model N callback initial
  .ok values

/-- Success of the concrete P6 array operation exposes its ordered trace. -/
theorem arrayFromFnP6_success_trace {T F : Type} (N : Usize)
    (callback : core.ops.function.FnMut F Usize T) (initial : F)
    {values : Aeneas.Std.Array T N}
    (h : arrayFromFnP6 N callback initial = .ok values) :
    ∃ final : F × Usize,
      AspisR1FromFnP6.StatefulFromFnTrace (fnMutStep callback) N.val 0
        (initial, 0#usize) values.val final := by
  unfold arrayFromFnP6 at h
  obtain ⟨pair, hmodel, hret⟩ := result_bind_ok_inv
    (core.array.from_fn_model N callback initial)
    (fun pair => do
      let (values, _final) := pair
      .ok values) (by simpa using h)
  rcases pair with ⟨array, final⟩
  have harray : array = values := Result.ok.inj hret
  have htrace := @core_array_from_fn_model_success_trace T F N callback initial
    array final hmodel
  rw [harray] at htrace
  exact ⟨final, htrace⟩

/-- Exact-ABI operation adapter for generated `FourDotsOps.arrayFromFn`.
Only this standard-library field is replaced; all other S4 operations are
inherited from `ops`. -/
def fourDotsOpsWithP6ArrayFromFn
    (ops : AspisR1FastDotsCurrent.FourDotsOps) :
    AspisR1FastDotsCurrent.FourDotsOps :=
  { ops with
    arrayFromFn := fun {T F} N callback initial =>
      if N.val = 4 then arrayFromFnP6 N callback initial
      else ops.arrayFromFn N callback initial }

/-- The adapted field, at the exact generated `FourDotsOps` type, returns the
same P6 state-threaded trace on every successful call. -/
theorem fourDotsOpsWithP6ArrayFromFn_success_trace
    (ops : AspisR1FastDotsCurrent.FourDotsOps)
    {T F : Type} (N : Usize)
    (callback : core.ops.function.FnMut F Usize T) (initial : F)
    {values : Aeneas.Std.Array T N}
    (hfour : N.val = 4)
    (h : (fourDotsOpsWithP6ArrayFromFn ops).arrayFromFn N callback initial =
      .ok values) :
    ∃ final : F × Usize,
      AspisR1FromFnP6.StatefulFromFnTrace (fnMutStep callback) N.val 0
        (initial, 0#usize) values.val final := by
  exact arrayFromFnP6_success_trace N callback initial
    (by simpa [fourDotsOpsWithP6ArrayFromFn, hfour] using h)

/-- The actual generated S4 outer callback instance has the exact trace
contract at the N=4 output-constructor call. -/
theorem fourDotsOuterGeneratedCallback_success_trace
    (ops : AspisR1FastDotsCurrent.FourDotsOps)
    (q1 : Aeneas.Std.Array Std.U8 608#usize)
    (g : Aeneas.Std.Array aspis_core.field.wide_exact.WideExact 29#usize)
    {values : Aeneas.Std.Array aspis_core.field.wide_exact.WideExact 4#usize}
    (h : (fourDotsOpsWithP6ArrayFromFn ops).arrayFromFn 4#usize
      (fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact
        (fourDotsOpsWithP6ArrayFromFn ops)) (q1, g) = .ok values) :
    ∃ final : fast_dots.four_dots.closure × Usize,
      AspisR1FromFnP6.StatefulFromFnTrace
        (fnMutStep
          (fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact
            (fourDotsOpsWithP6ArrayFromFn ops)))
        4 0 ((q1, g), 0#usize) values.val final := by
  exact fourDotsOpsWithP6ArrayFromFn_success_trace ops 4#usize
    (fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact
      (fourDotsOpsWithP6ArrayFromFn ops)) (q1, g) rfl h

#print axioms arrayFromFnP6_success_trace
#print axioms fourDotsOpsWithP6ArrayFromFn_success_trace
#print axioms fourDotsOuterGeneratedCallback_success_trace

end AspisR1FromFnP6Generated
