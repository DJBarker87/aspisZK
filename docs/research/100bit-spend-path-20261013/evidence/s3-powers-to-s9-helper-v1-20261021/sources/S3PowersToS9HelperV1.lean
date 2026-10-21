import S3PowersCanonicalTraceV1
import CurrentPowersExactProduct
import PowersP6IndexedOutputV1
import S3S9CurrentFieldOpsV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S3PowersToS9HelperV1

abbrev PowerWide := AspisR1PowersConcreteMul.CallbackWide
abbrev S9Wide := AspisR1S9CurrentFieldOpsV1.S
abbrev ExactWide := AspisR1CurrentWide.Proof.E

/-- Map the retained current-powers callback carrier into the nominal helper
carrier used by the scalar-factor source cut. The map is through the shared
eight-coordinate current-wide representation. -/
def powerToS9Helper (x : PowerWide) : S9Wide :=
  AspisR1S9CurrentFieldOpsV1.fromE (AspisR1PowersExactProduct.toFull x)

theorem powerToS9Helper_toE (x : PowerWide) :
    AspisR1S9CurrentFieldOpsV1.toE (powerToS9Helper x) =
      AspisR1PowersExactProduct.toFull x := by
  exact AspisR1S9CurrentFieldOpsV1.to_from _

theorem powerToS9Helper_canonical (x : PowerWide)
    (hx : AspisR1PowersConcreteMul.Canonical x) :
    AspisR1S9CurrentFieldOpsV1.Canonical (powerToS9Helper x) := by
  change AspisR1CurrentWide.Proof.CanonicalWide
    (AspisR1S9CurrentFieldOpsV1.toE (powerToS9Helper x))
  rw [powerToS9Helper_toE]
  exact hx

theorem powerToS9Helper_decode (x : PowerWide) :
    AspisR1S9CurrentFieldOpsV1.decode (powerToS9Helper x) =
      AspisR1PowersExactProduct.decode x := by
  change AspisR1CurrentWide.Proof.decodeWide
    (AspisR1S9CurrentFieldOpsV1.toE (powerToS9Helper x)) = _
  rw [powerToS9Helper_toE]
  rfl

/-- Every successful four-step retained powers trace yields scalar-factor
helper values with the same indexed power meaning. The Rust `from_fn`
correspondence and the caller assignment `ap0 := powers(alpha[0])` remain
outside this trace theorem. -/
theorem powers_trace_to_s9_helper_values
    (x : PowerWide) (values : List PowerWide)
    (final : AspisR1S3PowersCanonicalTraceV1.PowerState (4#usize))
    (hx : AspisR1PowersConcreteMul.Canonical x)
    (hrun : AspisR1FromFnP6.statefulFromFnRun
      (AspisR1S3PowersCanonicalTraceV1.powerStep (N := 4#usize))
      (4#usize).val 0
      (AspisR1CurrentPowers.field.WideExact.ONE, x) = .ok (values, final)) :
    ∀ i, i < 4 → ∃ helperValue,
      (values[i]?).map powerToS9Helper = some helperValue ∧
      AspisR1S9CurrentFieldOpsV1.Canonical helperValue ∧
      AspisR1S9CurrentFieldOpsV1.decode helperValue =
        AspisR1PowersExactProduct.decode x ^ i := by
  intro i hi
  have hfour : (4#usize).val = 4 := by decide
  have hi' : i < (4#usize).val := by simpa [hfour] using hi
  obtain ⟨value, hvalue, hcan, hdecode⟩ :=
    AspisR1PowersP6IndexedOutputV1.powersN_model_success_indexed
      (N := 4#usize) x values final hx hrun i hi'
  refine ⟨powerToS9Helper value, ?_, ?_, ?_⟩
  · simpa [hvalue]
  · exact powerToS9Helper_canonical value hcan
  · rw [powerToS9Helper_decode, hdecode]

#print axioms powerToS9Helper_toE
#print axioms powerToS9Helper_canonical
#print axioms powerToS9Helper_decode
#print axioms powers_trace_to_s9_helper_values

end AspisR1S3PowersToS9HelperV1
