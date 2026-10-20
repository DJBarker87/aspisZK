import S3PairLowCallStepBridgeV1

open Aeneas Aeneas.Std Result
set_option autoImplicit false

namespace AspisR1PairLowCallCut

open AspisR1S3PowersLowEntryCanonicalV1

theorem closure_left_getD (c : weights.s2_twofold_low_array.closure)
    (i : Nat) (hi : i < 4) :
    (closureToLowInputs c).1.getD i
      AspisR1CurrentPowers.field.WideExact.ONE =
      generatedToPower (c.1.val[i]'(by
        have h4 : (4#usize).val = 4 := by decide
        simpa [c.1.property, h4] using hi)) := by
  unfold closureToLowInputs
  have h4 : (4#usize).val = 4 := by decide
  have hlen : i < c.1.val.length := by
    simpa [c.1.property, h4] using hi
  have hlenMap : i < (c.1.val.map generatedToPower).length := by simpa using hlen
  rw [List.getD_eq_getElem _ _ hlenMap]
  simp

theorem closure_right_getD (c : weights.s2_twofold_low_array.closure)
    (i : Nat) (hi : i < 4) :
    (closureToLowInputs c).2.getD i
      AspisR1CurrentPowers.field.WideExact.ONE =
      generatedToPower (c.2.val[i]'(by
        have h4 : (4#usize).val = 4 := by decide
        simpa [c.2.property, h4] using hi)) := by
  unfold closureToLowInputs
  have h4 : (4#usize).val = 4 := by decide
  have hlen : i < c.2.val.length := by
    simpa [c.2.property, h4] using hi
  have hlenMap : i < (c.2.val.map generatedToPower).length := by simpa using hlen
  rw [List.getD_eq_getElem _ _ hlenMap]
  simp

#print axioms closure_left_getD
#print axioms closure_right_getD

end AspisR1PairLowCallCut
