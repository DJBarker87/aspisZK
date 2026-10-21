import AspisR1S9HelperP6.Funs
import S4FromFnP6GeneratedInterface

open Aeneas Aeneas.Std Result

namespace AspisR1S9HelperP6TraceV1

open AspisR1S9HelperP6
open AspisR1FromFnP6Generated

variable [AspisR1S9HelperP6.FieldOps]

/-- A successful generated `kpowers` result carries the exact ordered P6
callback trace, including the final closure and cursor. This only exposes the
reviewed P6 model trace; it does not assert Rust `from_fn` correspondence. -/
theorem kpowers_success_trace {N : Std.Usize} {x : field.QM31}
    {values : Array field.QM31 N}
    (h : weights.kpowers N x = .ok values) :
    ∃ final,
      AspisR1FromFnP6.StatefulFromFnTrace
        (AspisR1FromFnP6Generated.fnMutStep
          (weights.kpowers.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 N))
        N.val 0 ((field.QM31.ONE, x), 0#usize) values.val final := by
  unfold weights.kpowers at h
  obtain ⟨pair, hmodel, hreturn⟩ :=
    AspisR1FromFnP6Generated.result_bind_ok_inv
      (core.array.from_fn N
        (weights.kpowers.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 N)
        (field.QM31.ONE, x))
      (fun result => let (array, _) := result; .ok array) h
  rcases pair with ⟨array, final⟩
  have harray : array = values := Result.ok.inj hreturn
  subst values
  exact ⟨final,
    AspisR1FromFnP6Generated.core_array_from_fn_model_success_trace
      N (weights.kpowers.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 N)
      (field.QM31.ONE, x) hmodel⟩

#print axioms kpowers_success_trace

end AspisR1S9HelperP6TraceV1
