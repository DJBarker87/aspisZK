import S3ScalarFactorExtractedFoldTotalV1
import S3PowersToS9ScalarJoinV1
import S3S9ScalarFactorKpowersReadV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S3ScalarFactorPowersConstructiveS9V1

abbrev Ops := AspisR1S9HelperP6.FieldOps
abbrev S := AspisR1S9HelperP6.field.WideExact
abbrev Q := AspisR1S9HelperP6.field.QM31
abbrev PowerWide := AspisR1S3PowersToS9ScalarJoinV1.PowerWide
abbrev PowerState := AspisR1S3PowersCanonicalTraceV1.PowerState (4#usize)
abbrev Conclusion := AspisR1S3PowersToS9ScalarJoinV1.ScalarFactorS9Conclusion

/-- A successful canonical-input `kpowers` result and a successful canonical
N=4 powers trace feed the same concrete p/f arrays to scalar_factor. This
constructs its returned value and immediately joins that same value to the
retained S9 factored identity; the caller still supplies the array bindings. -/
theorem powers_trace_scalar_factor_constructively_s9
    (ops : Ops)
    (x : PowerWide) (values : List PowerWide) (final : PowerState)
    (hx : AspisR1PowersConcreteMul.Canonical x)
    (hrun : AspisR1FromFnP6.statefulFromFnRun
      (AspisR1S3PowersCanonicalTraceV1.powerStep (N := 4#usize))
      (4#usize).val 0
      (AspisR1CurrentPowers.field.WideExact.ONE, x) = .ok (values, final))
    (p : Array S (4#usize))
    (hmap : p.val = values.map AspisR1S3PowersToS9ScalarJoinV1.powerToS9Helper)
    (seed : Q) (f : Array Q (4#usize))
    (hseed : AspisR1CurrentWide.Proof.CanonicalQM
      (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM seed))
    (hpowers : @AspisR1S9HelperP6.weights.kpowers
      AspisR1S9HelperP6PowerSemanticsV1.currentFieldOps
      (4#usize) seed = .ok f)
    (b : Fin 4 → AspisR1S9TransparentFoldS2InstanceV1.E)
    (challenge1 : AspisR1S9TransparentFoldS2InstanceV1.E) (j : Fin 4) :
    ∃ out, Conclusion p f out seed b challenge1 j := by
  have hp := AspisR1S3PowersToS9ScalarJoinV1.mapped_power_array_index_canonical
    x values final hx hrun p hmap
  have hf : ∀ (index : Std.Usize) (value : Q),
      Array.index_usize f index = .ok value →
      AspisR1CurrentWide.Proof.CanonicalQM
        (AspisR1S9GeneratedWideMulQM31V2.toQM value) := by
    intro index value hread
    exact (AspisR1S9ScalarFactorKpowersReadV1.kpowers_success_read_current
      seed f hseed hpowers index value hread).1
  obtain ⟨out, hscalar⟩ :=
    AspisR1S3ScalarFactorExtractedFoldTotalV1.scalar_factor_total_with_extracted_fold
      ops p f hp hf
  exact ⟨out,
    AspisR1S3PowersToS9ScalarJoinV1.scalar_factor_on_powers_trace_with_s9_instance
      ops x values final hx hrun p hmap seed f out b challenge1 j hscalar hseed hpowers⟩

#print axioms powers_trace_scalar_factor_constructively_s9

end AspisR1S3ScalarFactorPowersConstructiveS9V1
