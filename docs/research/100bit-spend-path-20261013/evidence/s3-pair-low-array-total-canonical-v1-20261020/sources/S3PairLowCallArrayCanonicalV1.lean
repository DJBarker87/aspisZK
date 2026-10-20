import S3PairLowCallArrayProjectionV1

open Aeneas Aeneas.Std Result
set_option autoImplicit false

namespace AspisR1PairLowCallCut

abbrev LowInputs := AspisR1S3PowersLowEntryCanonicalV1.LowInputs
abbrev Canonical := AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.Canonical

/-- Canonical model outputs from V18 transport pointwise to the actual
WideExact callback values using the already proved sixteen-cell output map. -/
theorem actual_pair_low_array_output_canonical
    (c : weights.s2_twofold_low_array.closure)
    (hinputs : AspisR1S3PowersLowEntryCanonicalV1.lowInputsCanonical (closureToLowInputs c))
    (s : field.M31)
    (actual : Aeneas.Std.Array field.WideExact (16#usize))
    (actualFinal : weights.s2_twofold_low_array.closure × Usize)
    (model : Aeneas.Std.Array ActualS (16#usize))
    (modelFinal : LowInputs × Usize)
    (hscale : actualFieldOps.m31Mul weights.QUARTER weights.QUARTER = .ok s)
    (hactual : weights.s2_twofold_low_array_model actualFieldOps c.1 c.2 =
      .ok (actual,actualFinal))
    (hmodel : AspisR1FromFnP6Generated.core.array.from_fn_model (16#usize)
      (AspisR1S3PowersLowActualCanonicalV1.generatedLowCallback s)
      (closureToLowInputs c) =
        (.ok (model,modelFinal) : Result
          (Aeneas.Std.Array ActualS (16#usize) × (LowInputs × Usize))))
    (hmap : actual.val.map toActualS = model.val) :
    ∀ i : Fin 16,
      Canonical (toActualS (actual.val[i.val]'(by
        have hlen := actual.property
        change actual.val.length = (16#usize).val at hlen
        have hN : (16#usize).val = 16 := by decide
        omega))) := by
  have hcan := AspisR1S3PowersLowActualCanonicalV1.p6_generated_low_array_success_canonical s
    (closureToLowInputs c) model modelFinal hinputs hmodel
  intro i
  have hiA : i.val < actual.val.length := by
    have hlen := actual.property
    change actual.val.length = (16#usize).val at hlen
    have hN : (16#usize).val = 16 := by decide
    omega
  have hiM : i.val < model.val.length := by
    have hlen := model.property
    change model.val.length = (16#usize).val at hlen
    have hN : (16#usize).val = 16 := by decide
    omega
  have hopt := congrArg (fun xs : List ActualS => xs[i.val]?) hmap
  have hoptLeft : (actual.val.map toActualS)[i.val]? =
      some (toActualS (actual.val[i.val]'hiA)) := by
    simp only [List.getElem?_map, List.getElem?_eq_getElem hiA, Option.map_some]
  have hoptRight : model.val[i.val]? = some (model.val[i.val]'hiM) :=
    List.getElem?_eq_getElem hiM
  rw [hoptLeft, hoptRight] at hopt
  have hget : toActualS (actual.val[i.val]'hiA) = model.val[i.val]'hiM :=
    Option.some.inj hopt
  have hcanI : Canonical (model.val[i.val]'hiM) := hcan i
  exact hget.symm ▸ hcanI

#print axioms actual_pair_low_array_output_canonical

end AspisR1PairLowCallCut
