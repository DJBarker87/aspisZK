import S3PairLowCallArrayCanonicalV1

open Aeneas Aeneas.Std Result
set_option autoImplicit false

namespace AspisR1PairLowCallCut

/-- The focused callback cut has total output and canonical actual WideExact
values from a canonical input closure, with the callback's closure/cursor
postcondition retained. This composes the successful-run hypotheses away;
source correspondence to the enclosing Rust `Weights::pair` caller remains
separate. -/
theorem actual_pair_low_array_total_canonical
    (c : weights.s2_twofold_low_array.closure)
    (hinputs : AspisR1S3PowersLowEntryCanonicalV1.lowInputsCanonical
      (closureToLowInputs c)) :
    ∃ (s : field.M31)
      (actual : Aeneas.Std.Array field.WideExact (16#usize))
      (actualFinal : weights.s2_twofold_low_array.closure × Usize)
      (model : Aeneas.Std.Array ActualS (16#usize))
      (modelFinal : LowInputs × Usize),
      actualFieldOps.m31Mul weights.QUARTER weights.QUARTER = .ok s ∧
      weights.s2_twofold_low_array_model actualFieldOps c.1 c.2 =
        .ok (actual,actualFinal) ∧
      AspisR1FromFnP6Generated.core.array.from_fn_model (16#usize)
        (AspisR1S3PowersLowActualCanonicalV1.generatedLowCallback s)
        (closureToLowInputs c) =
        (.ok (model,modelFinal) : Result
          (Aeneas.Std.Array ActualS (16#usize) × (LowInputs × Usize))) ∧
      actual.val.map toActualS = model.val ∧
      (∀ i : Fin 16, Canonical (toActualS (actual.val[i.val]'(by
        have hlen := actual.property
        change actual.val.length = (16#usize).val at hlen
        have hN : (16#usize).val = 16 := by decide
        omega)))) ∧
      actualFinal.1 = c ∧ actualFinal.2.val = 16 := by
  obtain ⟨s,actual,actualFinal,model,modelFinal,hscale,hactual,hmodel,hmap,hclosure,hcursor⟩ :=
    AspisR1PairLowCallCut.actual_pair_low_array_total c hinputs
  have hcanonical := AspisR1PairLowCallCut.actual_pair_low_array_output_canonical
    c hinputs s actual actualFinal model modelFinal hscale hactual hmodel hmap
  refine ⟨s,actual,actualFinal,model,modelFinal,hscale,hactual,hmodel,hmap,hcanonical,?_,?_⟩
  · exact hclosure
  · have hN : (16#usize).val = 16 := by decide
    omega

#print axioms actual_pair_low_array_total_canonical

end AspisR1PairLowCallCut
