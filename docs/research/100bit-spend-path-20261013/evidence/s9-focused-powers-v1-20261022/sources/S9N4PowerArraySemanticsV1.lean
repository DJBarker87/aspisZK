import S3PowersCanonicalTraceV1
import S3PowersToS9ScalarJoinV1
import S3KpowersTotalConstructiveV1
import KpowersP6PowerSemanticsV1
import S3S9ConcreteFieldOpsV1

open Aeneas Aeneas.Std Result
set_option autoImplicit false

namespace AspisR1S9N4PowerArraySemanticsV1

open AspisR1S9HelperP6
open AspisR1S9HelperP6PowerSemanticsV1

local instance currentFieldOpsForSemantics :
    AspisR1S9HelperP6.FieldOps := currentFieldOps

abbrev PowerWide := AspisR1S3PowersToS9ScalarJoinV1.PowerWide
abbrev S9Wide := AspisR1S3PowersToS9ScalarJoinV1.S9Wide
abbrev HelperQM := AspisR1S9HelperP6.field.QM31

/-- From canonical low and high seeds, construct the retained N=4 low powers
trace and the helper's actual `kpowers` array under the concrete selected
field operations. The low array is the explicit S9 carrier map of that trace;
the high array is the output of the generated helper operation. Each returned
entry has its exact indexed power meaning. The enclosing caller's assignment
from its low powers call to `ap0`, and Rust `from_fn` correspondence, remain
separate source-boundary obligations. -/
theorem actual_s9_n4_low_high_arrays_from_canonical
    (x : PowerWide)
    (hx : AspisR1PowersConcreteMul.Canonical x)
    (seed : HelperQM)
    (hseed : currentQMSemantics.canonical seed) :
    ∃ (values : List PowerWide)
      (final : AspisR1S3PowersCanonicalTraceV1.PowerState (4#usize))
      (low : Array S9Wide (4#usize))
      (high : Array HelperQM (4#usize)),
      AspisR1FromFnP6.statefulFromFnRun
        (AspisR1S3PowersCanonicalTraceV1.powerStep (N := 4#usize))
        (4#usize).val 0
        (AspisR1CurrentPowers.field.WideExact.ONE, x) = .ok (values, final) ∧
      values.length = (4#usize).val ∧
      low.val = values.map AspisR1S3PowersToS9ScalarJoinV1.powerToS9Helper ∧
      (∀ i, i < 4 → ∃ v,
        low.val[i]? = some v ∧
        AspisR1S9CurrentFieldOpsV1.Canonical v ∧
        AspisR1S9CurrentFieldOpsV1.decode v =
          AspisR1PowersExactProduct.decode x ^ i) ∧
      @weights.kpowers AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        (4#usize) seed = .ok high ∧
      (∀ i, i < 4 → ∀ v, high.val[i]? = some v →
        currentQMSemantics.canonical v ∧
        currentQMSemantics.decode v = currentQMSemantics.decode seed ^ i) := by
  obtain ⟨values, final, hrun, hlen, _hcanonical, _hfinal⟩ :=
    AspisR1S3PowersCanonicalTraceV1.powersN_model_total
      (N := 4#usize) x hx
  let low : Array S9Wide (4#usize) :=
    AspisR1S3PowersToS9ScalarJoinV1.helperPowersArray values hlen
  have hlowmap : low.val =
      values.map AspisR1S3PowersToS9ScalarJoinV1.powerToS9Helper := rfl
  have hlowvalues :=
    AspisR1S3PowersToS9ScalarJoinV1.powers_trace_to_s9_helper_values
      x values final hx hrun
  obtain ⟨currentHigh, hcurrent⟩ :=
    AspisR1S3KpowersTotalConstructiveV1.kpowers_success_of_canonical_seed
      seed hseed
  have hconcrete :
      @weights.kpowers AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        (4#usize) seed =
      @weights.kpowers currentFieldOps (4#usize) seed := by
    simpa [currentFieldOps] using
      AspisR1S9ConcreteFieldOpsV1.kpowers_concrete_eq_current
        (4#usize) seed
  have hactual :
      @weights.kpowers AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        (4#usize) seed = .ok currentHigh := by
    rw [hconcrete]
    exact hcurrent
  have hhighvalues :=
    AspisR1S9HelperP6PowerSemanticsV1.kpowers_success_pointwise
      (sem := currentQMSemantics) hseed
      (N := 4#usize) (x := seed) (values := currentHigh) hcurrent
  refine ⟨values, final, low, currentHigh, hrun, hlen, hlowmap, ?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨v, hv, hcan, hdecode⟩ := hlowvalues i hi
    refine ⟨v, ?_, hcan, hdecode⟩
    simpa [hlowmap] using hv
  · exact hactual
  · intro i hi v hread
    have hfour : (4#usize).val = 4 := by decide
    have hi' : i < (4#usize).val := by omega
    exact hhighvalues i hi' v hread

#print axioms actual_s9_n4_low_high_arrays_from_canonical

end AspisR1S9N4PowerArraySemanticsV1
