import R0P.Occupancy
import ExtractedMaskQM31Exact
import SelectorExpansionCorrectness

/-! Exact fixed-array-to-retained-model list bridge for the 12 occupancy
residuals. The caller must supply each source cell's decoded formula; this
lemma only converts those twelve indexed facts into the model's list form. -/
set_option autoImplicit false
namespace AspisR1.OccupancyVectorBridge

open Aeneas Aeneas.Std

abbrev QM := AspisR1.ExtractedMaskQM31Exact.CurrentQM
abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact

private def exactVector (a : Array QM 12#usize) : Fin 12 → ExactQM :=
  fun i => AspisR1.ExtractedMaskQM31Exact.decode
    (a.val[i.val]'(by simpa [a.property] using i.isLt))

theorem cells_to_model_list
    (a : Array QM 12#usize)
    (input output expected : ExactQM) (opened : Fin 16 → ExactQM)
    (hcells : ∀ i : Fin 12,
      AspisR1.ExtractedMaskQM31Exact.decode
        (a.val[i.val]'(by simpa [a.property] using i.isLt)) =
        (R0P.occupancyLanesLiteral input output expected opened)[i.val]'(by
          simp [R0P.occupancyLanesLiteral])) :
    List.ofFn (exactVector a) = R0P.occupancyLanesLiteral input output expected opened := by
  apply List.ext_getElem
  · simp [R0P.occupancyLanesLiteral]
  · intro n hleft hright
    have hn : n < 12 := by simpa [R0P.occupancyLanesLiteral] using hright
    rw [List.getElem_ofFn]
    simpa [exactVector] using hcells ⟨n, hn⟩

#print axioms cells_to_model_list
end AspisR1.OccupancyVectorBridge
