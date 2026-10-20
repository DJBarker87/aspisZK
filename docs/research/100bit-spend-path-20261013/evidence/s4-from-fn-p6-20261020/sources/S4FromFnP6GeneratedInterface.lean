import Aeneas.Std.Array.Array
import S4FromFnP6GeneratedTrace

open Aeneas Aeneas.Std Result
set_option autoImplicit false

namespace AspisR1FromFnP6Generated

theorem result_bind_ok_inv {A B : Type} (r : Result A) (k : A → Result B)
    {out : B} (h : (do let x ← r; k x) = .ok out) :
    ∃ x, r = .ok x ∧ k x = .ok out := by
  cases r with
  | fail e => simp at h
  | div => simp at h
  | ok value => exact ⟨value, rfl, h⟩

/-- Convert a successful stateful list run to the fixed-length Aeneas array,
preserving failures and divergence. -/
def packArrayState {T S : Type} (N : Usize) :
    Result (List T × S) → Result (Aeneas.Std.Array T N × S)
  | .fail e => .fail e
  | .div => .div
  | .ok (values, final) =>
      if hlen : values.length = N.val then
        .ok (⟨values, hlen⟩, final)
      else .div

/-- Array-valued model at the generated Aeneas callback ABI. -/
def core.array.from_fn_model {T F : Type}
    (N : Usize) (callback : core.ops.function.FnMut F Usize T) (initial : F) :
    Result (Aeneas.Std.Array T N × (F × Usize)) :=
  packArrayState N (core.array.from_fn_trace_model N callback initial)

/-- Success exposes the ordered callback trace and its final closure/index. -/
theorem core_array_from_fn_model_success_trace {T F : Type}
    (N : Usize) (callback : core.ops.function.FnMut F Usize T) (initial : F)
    {values : Aeneas.Std.Array T N} {final : F × Usize}
    (h : core.array.from_fn_model N callback initial = .ok (values, final)) :
    AspisR1FromFnP6.StatefulFromFnTrace (fnMutStep callback) N.val 0
      (initial, 0#usize) values.val final := by
  unfold core.array.from_fn_model at h
  cases hr : core.array.from_fn_trace_model N callback initial with
  | fail e => simp [packArrayState, hr] at h
  | div => simp [packArrayState, hr] at h
  | ok pair =>
      rcases pair with ⟨items, state⟩
      have hrun : AspisR1FromFnP6.statefulFromFnRun (fnMutStep callback)
          N.val 0 (initial, 0#usize) = .ok (items, state) := by
        simpa only [core.array.from_fn_trace_model] using hr
      have hlen := fnMutRun_values_length N callback initial hrun
      simp only [packArrayState, hr, dif_pos hlen] at h
      have hp := Result.ok.inj h
      rcases Prod.mk.inj hp with ⟨harray, hstate⟩
      have hitems : items = values.val := congrArg Subtype.val harray
      have htrace := (core_array_from_fn_trace_model_success_iff
        N callback initial items state).mp hr
      subst state
      rw [← hitems]
      exact htrace

#print axioms core_array_from_fn_model_success_trace

end AspisR1FromFnP6Generated
