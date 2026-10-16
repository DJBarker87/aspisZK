import SelectorReconstructIndexedCanonical
import SelectorReconstructIndexModel
import R0P.Value

/-! Canonicality and model correspondence for the explicit descending-index
reconstruction recurrence. The generated candidate still needs a source proof
that its Rust loop is exactly this recurrence; that extraction/refinement step
is separate. -/
set_option autoImplicit false
namespace AspisR1.SelectorReconstructTenBridge

open Aeneas Aeneas.Std
open AspisR1.SelectorReconstructIndexedCanonical
open AspisR1.SelectorReconstructIndexModel
open AspisR1SelectedMaskProbe
open AspisR1.ExtractedMaskQM31Exact

abbrev QM := field.QM31
abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact
abbrev Canonical := AspisR1.ExtractedMaskTowerAdd.CanonicalQM

/-- For a canonical ten-cell view, any successful evaluation of the explicit
nine-step checked reverse recurrence is canonical and decodes to R0P's
`valueReconstruct10` on the same cells. -/
theorem checked_reconstruct_10_success
    (view : Nat → QM) (out : QM)
    (hview : ∀ i, i ≤ 9 → Canonical (view i))
    (hrun : checkedReconstructIndexed (fun i => view i) 9 (view 9) = .ok out) :
    Canonical out ∧
      decode out = R0P.valueReconstruct10
        (fun i : Fin 16 => decode (view i.val)) := by
  have hacc : Canonical (view 9) := hview 9 (by omega)
  have hbits : ∀ i, i < 9 → Canonical (view i) := by
    intro i hi
    exact hview i (by omega)
  obtain ⟨hout, hdecode⟩ :=
    checkedReconstructIndexed_success_canonical view 9 (view 9) out hacc hbits hrun
  refine ⟨hout, ?_⟩
  calc
    decode out = reconstructIndexed (fun i => decode (view i)) 9 (decode (view 9)) := hdecode
    _ = R0P.valueReconstruct10 (fun i : Fin 16 => decode (view i.val)) := by
      simpa only using reconstructIndexed_nine_eq_valueReconstruct10
        (fun i : Nat => decode (view i))

#print axioms checked_reconstruct_10_success
end AspisR1.SelectorReconstructTenBridge
