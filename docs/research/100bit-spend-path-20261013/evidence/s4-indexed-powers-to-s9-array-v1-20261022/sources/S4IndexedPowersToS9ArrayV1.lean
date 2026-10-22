import LoopPowersEarlyTotal
import S3PowersToS9ScalarJoinV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S4IndexedPowersToS9ArrayV1

abbrev PowerWide := AspisR1PowersConcreteMul.CallbackWide
abbrev S9Wide := AspisR1S3PowersToS9ScalarJoinV1.S9Wide
abbrev LoopWide := AspisR1LoopPowers.field.WideExact
abbrev Four := 4#usize

open AspisR1LoopPowers
open AspisR1S3PowersToS9ScalarJoinV1

/-- Map the extracted indexed-powers carrier into the exact helper-array
carrier consumed by the retained S9 scalar-factor theorem. This is only a
structural carrier map; the source function itself is pinned by the adjacent
source checker. -/
def loopArrayToS9 (values : Array LoopWide Four) : Array S9Wide Four :=
  helperPowersArray (values.val.map toOld) (by
    simpa only [List.length_map] using values.property)

/-- The N=4 instance of the proved indexed early-return powers body, mapped to
the same PowerWide/S9Wide carriers used by the S9 helper. -/
def earlyPowers4ToS9 (x : PowerWide) : Result (Array S9Wide Four) := do
  let values ← weights.early_powers Four (fromOld x)
  .ok (loopArrayToS9 values)

/-- The candidate early-return powers body is total on a canonical N=4 base.
Each returned element is the same indexed power, transported through the
checked current-Powers and S9 helper carrier maps. -/
theorem early_powers4_to_s9_total_exact (x : PowerWide)
    (hx : AspisR1PowersConcreteMul.Canonical x) :
    ∃ out, earlyPowers4ToS9 x = .ok out ∧
      ∀ j : Fin Four.val,
        AspisR1S9CurrentFieldOpsV1.Canonical
          (out.val[j.val]'(by rw [out.property]; exact j.isLt)) ∧
        AspisR1S9CurrentFieldOpsV1.decode
          (out.val[j.val]'(by rw [out.property]; exact j.isLt)) =
          AspisR1PowersExactProduct.decode x ^ j.val := by
  have hxLoop : Canonical (fromOld x) := by
    change AspisR1PowersConcreteMul.Canonical (toOld (fromOld x))
    rw [to_from_old]
    exact hx
  obtain ⟨values, hvalues, hmeaning⟩ :=
    early_powers_total_exact Four (fromOld x) hxLoop
  refine ⟨loopArrayToS9 values, ?_, ?_⟩
  · simp only [earlyPowers4ToS9, hvalues, bind_tc_ok]
  · intro j
    have hvalue := hmeaning j
    have hmapIndex :
        (loopArrayToS9 values).val[j.val]'(by
          rw [loopArrayToS9, helperPowersArray]
          simp only [List.length_map]
          rw [values.property]
          exact j.isLt) =
        powerToS9Helper (toOld (values.val[j.val]'(by
          rw [values.property]
          exact j.isLt))) := by
      simp only [loopArrayToS9, helperPowersArray, List.getElem_map,
        powerToS9Helper]
    rw [hmapIndex]
    rcases hvalue with ⟨hcan, hdecode⟩
    constructor
    · exact powerToS9Helper_canonical _ hcan
    · rw [powerToS9Helper_decode]
      change AspisR1PowersExactProduct.decode
        (toOld (values.val[j.val]'(by rw [values.property]; exact j.isLt))) =
        AspisR1PowersExactProduct.decode x ^ j.val
      change AspisR1PowersExactProduct.decode
        (toOld (values.val[j.val]'(by rw [values.property]; exact j.isLt))) =
        AspisR1PowersExactProduct.decode
          (toOld (fromOld x)) ^ j.val at hdecode
      rw [to_from_old] at hdecode
      exact hdecode

#print axioms early_powers4_to_s9_total_exact

end AspisR1S4IndexedPowersToS9ArrayV1
