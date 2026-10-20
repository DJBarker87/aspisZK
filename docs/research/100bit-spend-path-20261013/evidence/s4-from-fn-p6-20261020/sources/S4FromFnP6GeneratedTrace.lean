import StatefulArrayFromFnModelV1

/-!
Operational P6 boundary for generated Aeneas `core.array.from_fn`.  This
defines the generated `FnMut` callback invocation at its exact Aeneas ABI and
threads the callback-returned state together with the Usize cursor.  The
resulting list is the array's ordered backing values in the reviewed model.
The Rust standard-library correspondence remains P6, supported by the pinned
Rust differential test.
-/
open Aeneas Aeneas.Std Result
set_option autoImplicit false

namespace AspisR1FromFnP6Generated

/-- One generated `from_fn` step: call the supplied FnMut record, retain its
returned closure state, and advance the same Usize index. -/
def fnMutStep {T F : Type}
    (callback : core.ops.function.FnMut F Usize T)
    (state : F × Usize) (_index : Nat) : Result (T × (F × Usize)) := do
  let (value, state') ← callback.call_mut state.1 state.2
  let index' ← state.2 + 1#usize
  .ok (value, (state', index'))

/-- The P6 model specialized to the exact generated from_fn callback ABI. -/
def core.array.from_fn_trace_model {T F : Type}
    (N : Usize) (callback : core.ops.function.FnMut F Usize T) (initial : F) :
    Result (List T × (F × Usize)) :=
  AspisR1FromFnP6.statefulFromFnRun (fnMutStep callback) N.val 0
    (initial, 0#usize)

/-- A successful generated-interface model run is exactly an ordered
state-threaded callback trace. -/
theorem core_array_from_fn_trace_model_success_iff {T F : Type}
    (N : Usize) (callback : core.ops.function.FnMut F Usize T) (initial : F)
    (values : List T) (final : F × Usize) :
    core.array.from_fn_trace_model N callback initial = .ok (values, final) ↔
      AspisR1FromFnP6.StatefulFromFnTrace (fnMutStep callback) N.val 0
        (initial, 0#usize) values final := by
  exact AspisR1FromFnP6.statefulFromFnRun_success_iff_trace
    (fnMutStep callback) N.val 0 (initial, 0#usize) values final

/-- The generated-interface model emits exactly one value per requested
index. -/
theorem fnMutRun_values_length {T F : Type}
    (N : Usize) (callback : core.ops.function.FnMut F Usize T) (initial : F)
    {values : List T} {final : F × Usize}
    (hrun : AspisR1FromFnP6.statefulFromFnRun (fnMutStep callback) N.val 0
      (initial, 0#usize) = .ok (values, final)) :
    values.length = N.val := by
  exact AspisR1FromFnP6.statefulFromFnTrace_length
    ((core_array_from_fn_trace_model_success_iff N callback initial values final).mp
      (by simpa [core.array.from_fn_trace_model] using hrun))

#print axioms core_array_from_fn_trace_model_success_iff
#print axioms fnMutRun_values_length

end AspisR1FromFnP6Generated
