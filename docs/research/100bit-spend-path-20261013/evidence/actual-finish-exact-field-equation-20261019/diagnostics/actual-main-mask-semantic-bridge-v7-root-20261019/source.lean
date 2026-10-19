import ActualFinishConcreteArithmeticBoundary
import ExtractedMaskSemanticBridgeConcrete

/-! Interpret the concrete selected-mask operation used by finish in the
existing WideExact privacy/soundness mask model. Input canonicality is an
explicit obligation; the mask value equation is derived from extracted code. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1PublicPreparation.ActualMainMaskSemanticBridge
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.RawSemanticFieldOwnerAdapter
open AspisR1PublicPreparation.ActualFinishConcreteArithmeticBoundary

abbrev E := AspisWideTower.WideExact

def fieldValue (x : MainQM) : E :=
  algebraMap AspisR1.ExtractedMaskQM31Exact.QM31Exact E
    (AspisR1.ExtractedMaskQM31Exact.decode (mainToProbe x))

def CanonicalArray {n : Usize} (xs : Array MainQM n) : Prop :=
  ∀ i : Fin n.val, Canonical
    (mainToProbe (xs.val[i.val]'(by simpa [xs.property] using i.isLt)))

def cell {n : Usize} (xs : Array MainQM n) (i : Fin n.val) : MainQM :=
  xs.val[i.val]'(by simpa [xs.property] using i.isLt)

def maskValue (c1 : Array MainQM 16#usize) (maskOnly : Array MainQM 10#usize)
    (g : MainQM) (point : Array MainQM 10#usize) : E :=
  R0P.Mask.maskValue AspisR1.ExtractedMaskSemanticBridgeConcrete.packBasis
    (fun j => fieldValue (cell c1 j))
    (fun j => fieldValue (cell maskOnly j))
    (fieldValue g) (fun i => fieldValue (cell point i))

private theorem mapped_cell {n : Usize} (xs : Array MainQM n) (i : Fin n.val) :
    (mainArrayToProbeN xs).val[i.val]'(by
      simpa [(mainArrayToProbeN xs).property] using i.isLt) =
      mainToProbe (cell xs i) := by
  simp only [mainArrayToProbeN, cell, List.getElem_map]

/-- The actual selected-mask body produces a canonical result with exactly the
already defined R0P mask meaning after the coordinate-owner isomorphism. -/
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
    AspisR1.ExtractedMaskSemanticBridgeConcrete.current_selected_mask_maps_to_maskValue
      (mainArrayToProbeN c1) (mainArrayToProbeN maskOnly) (mainToProbe g)
      (mainArrayToProbeN point) hc1' hmask' hpoint' hg
  refine ⟨probeToMain out, ?_, ?_, ?_⟩
  · simp only [extractedMainMask, hrun, probeResultToMain]
  · simpa only [mainToProbe_probeToMain] using hcanonical
  · have hmain : fieldValue (probeToMain out) =
        AspisR1.ExtractedMaskSemanticBridgeConcrete.qm31ToWide
          (AspisR1.ExtractedMaskQM31Exact.decode out) := by
      unfold fieldValue AspisR1.ExtractedMaskSemanticBridgeConcrete.qm31ToWide
      rw [mainToProbe_probeToMain]
    refine (hmain.trans hvalue).trans ?_
    dsimp only [maskValue]
    congr 1
    · funext j
      change AspisR1.ExtractedMaskSemanticBridgeConcrete.qm31ToWide
        (AspisR1.ExtractedMaskQM31Exact.decode
          ((mainArrayToProbeN c1).val[j.val]'(by
            simpa [(mainArrayToProbeN c1).property] using j.isLt))) = _
      rw [mapped_cell]
      rfl
    · funext j
      change AspisR1.ExtractedMaskSemanticBridgeConcrete.qm31ToWide
        (AspisR1.ExtractedMaskQM31Exact.decode
          ((mainArrayToProbeN maskOnly).val[j.val]'(by
            simpa [(mainArrayToProbeN maskOnly).property] using j.isLt))) = _
      rw [mapped_cell]
      rfl
    · funext j
      change AspisR1.ExtractedMaskSemanticBridgeConcrete.qm31ToWide
        (AspisR1.ExtractedMaskQM31Exact.decode
          ((mainArrayToProbeN point).val[j.val]'(by
            simpa [(mainArrayToProbeN point).property] using j.isLt))) = _
      rw [mapped_cell]
      rfl

#print axioms extractedMainMask_refines
end AspisR1PublicPreparation.ActualMainMaskSemanticBridge
end
