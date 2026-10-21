import S3ScalarFactorPowersConstructiveS9V1
import S3KpowersTotalConstructiveV1

open Aeneas Aeneas.Std Result
set_option autoImplicit false

namespace AspisR1S3ScalarFactorPowersNoHpowersV1

abbrev Ops := AspisR1S9HelperP6.FieldOps
abbrev S := AspisR1S9HelperP6.field.WideExact
abbrev Q := AspisR1S9HelperP6.field.QM31
abbrev PowerWide := AspisR1S3PowersToS9ScalarJoinV1.PowerWide
abbrev PowerState := AspisR1S3PowersCanonicalTraceV1.PowerState (4#usize)
abbrev Conclusion := AspisR1S3PowersToS9ScalarJoinV1.ScalarFactorS9Conclusion

/-- The retained P6 powers trace, explicit caller p-array map, and canonical
seed suffice for the constructive scalar-factor/S9 result. The helper `kpowers`
success premise is derived from the exact current QM multiply operation rather
than supplied by the caller. The `p` assignment and Rust array-library
correspondence remain separate caller/P6 boundaries. -/
theorem powers_trace_scalar_factor_constructively_s9_no_hpowers
    (ops : Ops)
    (x : PowerWide) (values : List PowerWide) (final : PowerState)
    (hx : AspisR1PowersConcreteMul.Canonical x)
    (hrun : AspisR1FromFnP6.statefulFromFnRun
      (AspisR1S3PowersCanonicalTraceV1.powerStep (N := 4#usize))
      (4#usize).val 0
      (AspisR1CurrentPowers.field.WideExact.ONE, x) = .ok (values, final))
    (p : Array S (4#usize))
    (hmap : p.val = values.map AspisR1S3PowersToS9ScalarJoinV1.powerToS9Helper)
    (seed : Q) (b : Fin 4 → AspisR1S9TransparentFoldS2InstanceV1.E)
    (challenge1 : AspisR1S9TransparentFoldS2InstanceV1.E) (j : Fin 4)
    (hseed : AspisR1CurrentWide.Proof.CanonicalQM
      (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM seed)) :
    ∃ f out, @AspisR1S9HelperP6.weights.kpowers
        AspisR1S9HelperP6PowerSemanticsV1.currentFieldOps (4#usize) seed = .ok f ∧
      Conclusion p f out seed b challenge1 j := by
  letI : Ops := AspisR1S9HelperP6PowerSemanticsV1.currentFieldOps
  have hseed' : AspisR1S9HelperP6PowerSemanticsV1.currentQMSemantics.canonical seed := by
    change AspisR1CurrentWide.Proof.CanonicalQM
      (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM seed)
    exact hseed
  obtain ⟨f,hpowers⟩ :=
    AspisR1S3KpowersTotalConstructiveV1.kpowers_success_of_canonical_seed seed hseed'
  obtain ⟨out,hconclusion⟩ :=
    AspisR1S3ScalarFactorPowersConstructiveS9V1.powers_trace_scalar_factor_constructively_s9
      ops x values final hx hrun p hmap seed f hseed hpowers b challenge1 j
  exact ⟨f,out,hpowers,hconclusion⟩

#print axioms powers_trace_scalar_factor_constructively_s9_no_hpowers

end AspisR1S3ScalarFactorPowersNoHpowersV1
