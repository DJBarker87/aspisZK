import S3S9ScalarFactorKpowersReadV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9ScalarFactorPowerArrayMeaningV1

abbrev Q := AspisR1S9HelperP6.field.QM31
abbrev U := Std.Usize

/-- The same successful selected four-entry `kpowers` result gives exact
decoded powers at every successful in-range source read. This is the value
companion to the canonical-read bridge used by scalar_factor. -/
theorem kpowers_array_read_power_value
    (seed : Q) (values : Array Q (4#usize))
    (hseed : AspisR1CurrentWide.Proof.CanonicalQM
      (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM seed))
    (hpowers : @AspisR1S9HelperP6.weights.kpowers
      AspisR1S9HelperP6PowerSemanticsV1.currentFieldOps
      (4#usize) seed = .ok values) :
    ∀ (index : U) (value : Q),
      Array.index_usize values index = .ok value →
      AspisR1CurrentWide.Proof.decodeQM
        (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM value) =
      AspisR1CurrentWide.Proof.decodeQM
        (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM seed) ^ index.val := by
  intro index value hread
  exact (AspisR1S9ScalarFactorKpowersReadV1.kpowers_success_read_current
    seed values hseed hpowers index value hread).2

#print axioms kpowers_array_read_power_value

end AspisR1S9ScalarFactorPowerArrayMeaningV1
