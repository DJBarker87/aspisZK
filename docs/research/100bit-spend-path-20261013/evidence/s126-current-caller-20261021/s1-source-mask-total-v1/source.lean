import S1SourceMaskOpsV1
import ExtractedMaskCallerModel
set_option autoImplicit false
namespace AspisS1SourceMaskOps
open Aeneas Aeneas.Std Result

def Canonical (q : MainQM) : Prop :=
  (q.c0.a.val<2147483647 ∧ q.c0.b.val<2147483647) ∧
  (q.c1.a.val<2147483647 ∧ q.c1.b.val<2147483647)

/-- TOTAL concrete source mask on its canonical input domain. Both coefficient
loops, Horner/linear loops and all intermediate arithmetic are derived by the
reused complete mask proof, checked against the current source imports. -/
theorem mask_total (first : Array MainQM 16#usize) (second : Array MainQM 10#usize)
    (g : MainQM) (alpha : Array MainQM 10#usize)
    (hf : ∀ q ∈ first.val, Canonical q) (hs : ∀ q ∈ second.val, Canonical q)
    (hg : Canonical g) (ha : ∀ q ∈ alpha.val, Canonical q) :
    ∃ value, mask first second g alpha=ok value ∧ Canonical value := by
  have cf : ∀ i : Fin 16,
      AspisR1.ExtractedMaskCallerModel.CanonicalQM
        (AspisR1.ExtractedMaskCoefficientStep.c1Cell (probeArray first) i) := by
    intro i
    have h := hf (first.val[i.val]'(by simpa [first.property] using i.isLt)) (List.getElem_mem _)
    simpa only [AspisR1.ExtractedMaskCoefficientStep.c1Cell,probeArray,List.getElem_map] using h
  have cs : ∀ i : Fin 10,
      AspisR1.ExtractedMaskCallerModel.CanonicalQM
        (AspisR1.ExtractedMaskCoefficientStep.maskCell (probeArray second) i) := by
    intro i
    have h := hs (second.val[i.val]'(by simpa [second.property] using i.isLt)) (List.getElem_mem _)
    simpa only [AspisR1.ExtractedMaskCoefficientStep.maskCell,probeArray,List.getElem_map] using h
  have ca : ∀ i : Nat, ∀ hi : i<10,
      AspisR1.ExtractedMaskCallerModel.CanonicalQM
        (AspisR1.ExtractedMaskLinearLoop.pointAtNat (probeArray alpha) i hi) := by
    intro i hi
    have h := ha (alpha.val[i]'(by simpa [alpha.property] using hi)) (List.getElem_mem _)
    simpa only [AspisR1.ExtractedMaskLinearLoop.pointAtNat,probeArray,List.getElem_map] using h
  have cg : AspisR1.ExtractedMaskCallerModel.CanonicalQM (toProbe g) := hg
  obtain ⟨value,called,canonical,_⟩ :=
    AspisR1.ExtractedMaskCallerModel.selected_mask_value_populated_model
      (probeArray first) (probeArray second) (toProbe g) (probeArray alpha) cf cs ca cg
  refine ⟨fromProbe value,?_,?_⟩
  · simp only [mask,called,resultFromProbe]
  · exact canonical

#print axioms mask_total
end AspisS1SourceMaskOps
