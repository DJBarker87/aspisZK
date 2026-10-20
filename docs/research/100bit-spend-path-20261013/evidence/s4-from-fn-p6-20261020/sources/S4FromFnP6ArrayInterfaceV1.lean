import Aeneas.Std.Array.Array
import S4FromFnP6GeneratedTrace

open Aeneas Aeneas.Std Result
set_option autoImplicit false

namespace AspisR1FromFnP6Generated

/-- Convert a successful stateful list run to the fixed-length Aeneas array.
The failure and divergence cases are preserved exactly. -/
def packArrayState {T S : Type} (N : Usize) :
    Result (List T × S) → Result (Aeneas.Std.Array T N × S)
  | .fail e => .fail e
  | .div => .div
  | .ok (values, final) =>
      if hlen : values.length = N.val then
        .ok (⟨values, hlen⟩, final)
      else .div

/-- Array-valued generated-interface model. -/
def core.array.from_fn_array_model {T F : Type}
    (N : Usize) (callback : core.ops.function.FnMut F Usize T) (initial : F) :
    Result (Aeneas.Std.Array T N × (F × Usize)) :=
  packArrayState N (core.array.from_fn_trace_model N callback initial)

/-- A successful array model run yields the exact ordered callback trace and
the final closure/index state. -/
theorem core_array_from_fn_array_model_success_trace {T F : Type}
    (N : Usize) (callback : core.ops.function.FnMut F Usize T) (initial : F)
    {values : Aeneas.Std.Array T N} {final : F × Usize}
    (h : core.array.from_fn_array_model N callback initial = .ok (values, final)) :
    AspisR1FromFnP6.StatefulFromFnTrace (fnMutStep callback) N.val 0
      (initial, 0#usize) values.val final := by
  unfold core.array.from_fn_array_model core.array.from_fn_trace_model at h
  cases hr : AspisR1FromFnP6.statefulFromFnRun (fnMutStep callback) N.val 0
      (initial, 0#usize) with
  | fail e => simp [packArrayState, hr] at h
  | div => simp [packArrayState, hr] at h
  | ok pair =>
      rcases pair with ⟨items, state⟩
      have hlen := fnMutRun_values_length N callback initial (by simpa [hr])
      simp only [packArrayState, hr, hlen, dif_pos, bind_tc_ok] at h
      have hp := Result.ok.inj h
      have hitems : items = values.val := congrArg Subtype.val hp.1
      have hstate : state = final := hp.2
      subst state
      subst items
      exact (core_array_from_fn_trace_model_success_iff N callback initial
        values.val final).mp (by simpa [core.array.from_fn_trace_model, hr])

#print axioms core_array_from_fn_array_model_success_trace

end AspisR1FromFnP6Generated
