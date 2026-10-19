import ActualFinishConcreteArithmeticBoundary

/-! Interpret the concrete selected-mask operation used by finish in the
existing populated-coefficient exact-field model. Input canonicality is an
explicit obligation; the mask value equation is derived from extracted code. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1PublicPreparation.ActualMainMaskPopulatedBridge
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.RawSemanticFieldOwnerAdapter
open AspisR1PublicPreparation.ActualFinishConcreteArithmeticBoundary

abbrev E := AspisR1.ExtractedMaskQM31Exact.QM31Exact

def fieldValue (x : MainQM) : E :=
  AspisR1.ExtractedMaskQM31Exact.decode (mainToProbe x)

def CanonicalArray {n : Usize} (xs : Array MainQM n) : Prop :=
  ∀ i : Fin n.val, Canonical
    (mainToProbe (xs.val[i.val]'(by simpa [xs.property] using i.isLt)))

def cell {n : Usize} (xs : Array MainQM n) (i : Fin n.val) : MainQM :=
  xs.val[i.val]'(by simpa [xs.property] using i.isLt)

def maskValue (c1 : Array MainQM 16#usize) (maskOnly : Array MainQM 10#usize)
    (g : MainQM) (point : Array MainQM 10#usize) : E :=
  AspisR1.ExtractedMaskHornerPolynomial.coefficientPolynomial
    (AspisR1.ExtractedMaskHornerCaller.coefficientValue
      (AspisR1.ExtractedMaskCallerModel.populatedCoefficients
        (mainArrayToProbeN c1) (mainArrayToProbeN maskOnly)))
    (AspisR1.ExtractedMaskLinearRecurrence.maskLinear 0
      (AspisR1.ExtractedMaskLinearsExact.decodedPoint (mainArrayToProbeN point))) +
    (1 + (AspisR1.ExtractedMaskLinearRecurrence.maskLinear 16
      (AspisR1.ExtractedMaskLinearsExact.decodedPoint (mainArrayToProbeN point))) ^ 26) *
      fieldValue g

/-- The actual selected-mask body produces a canonical result with exactly the
already proved populated-coefficient mask meaning after the coordinate-owner isomorphism. -/
theorem extractedMainMask_refines
    (c1 : Array MainQM 16#usize) (maskOnly : Array MainQM 10#usize)
    (g : MainQM) (point : Array MainQM 10#usize)
    (hc1 : CanonicalArray c1) (hmask : CanonicalArray maskOnly)
    (hg : Canonical (mainToProbe g)) (hpoint : CanonicalArray point) :
    ∃ out : MainQM,
      extractedMainMask c1 maskOnly g point = .ok out ∧
      Canonical (mainToProbe out) ∧
      fieldValue out = maskValue c1 maskOnly g point := by
  have hc1' : ∀ j : Fin 16,
      AspisR1.ExtractedMaskCoefficientStep.CanonicalQM
        (AspisR1.ExtractedMaskCoefficientStep.c1Cell (mainArrayToProbeN c1) j) := by
    intro j
    simpa only [AspisR1.ExtractedMaskCoefficientStep.c1Cell,
      mainArrayToProbeN, List.getElem_map] using hc1 j
  have hmask' : ∀ j : Fin 10,
      AspisR1.ExtractedMaskCoefficientStep.CanonicalQM
        (AspisR1.ExtractedMaskCoefficientStep.maskCell (mainArrayToProbeN maskOnly) j) := by
    intro j
    simpa only [AspisR1.ExtractedMaskCoefficientStep.maskCell,
      mainArrayToProbeN, List.getElem_map] using hmask j
  have hpoint' : ∀ i : Nat, ∀ hi : i < 10,
      AspisR1.ExtractedMaskLinearLoop.CanonicalQM
        (AspisR1.ExtractedMaskLinearLoop.pointAtNat (mainArrayToProbeN point) i hi) := by
    intro i hi
    simpa only [AspisR1.ExtractedMaskLinearLoop.pointAtNat,
      mainArrayToProbeN, List.getElem_map] using hpoint ⟨i, hi⟩
  obtain ⟨out, hrun, hcanonical, hvalue⟩ :=
    AspisR1.ExtractedMaskCallerModel.selected_mask_value_populated_model
      (mainArrayToProbeN c1) (mainArrayToProbeN maskOnly) (mainToProbe g)
      (mainArrayToProbeN point) hc1' hmask' hpoint' hg
  refine ⟨probeToMain out, ?_, ?_, ?_⟩
  · simp only [extractedMainMask, hrun, probeResultToMain]
  · simpa only [mainToProbe_probeToMain] using hcanonical
  · simpa only [fieldValue, maskValue, mainToProbe_probeToMain] using hvalue

#print axioms extractedMainMask_refines
end AspisR1PublicPreparation.ActualMainMaskPopulatedBridge
end
