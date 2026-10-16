import SelectorValueLaneModelComposition
import ExtractedMaskQmPackBase4Semantic

/-! Transport the proved source tensor selectors to the same lifted point
used by the WideExact relation. Reuses the finite-product homomorphism proof
pattern in AspisV8R19.FullWeightHom.map_point_basis and
AspisV8R19.R374SingleCoordinateDegree.claim_eval, without importing their
unrelated certificate/degree cone. -/
set_option autoImplicit false
namespace AspisR1.SelectorFieldTransport
noncomputable section

theorem map_tensor {K L : Type} [CommRing K] [CommRing L]
    (g : K →+* L) (z : Nat → K) (n row : Nat) :
    g (AspisV8.SelectedSelectorExpansion.tensorProduct z n row) =
      AspisV8.SelectedSelectorExpansion.tensorProduct (fun i => g (z i)) n row := by
  simp only [AspisV8.SelectedSelectorExpansion.tensorProduct,
    AspisV8.SelectedSelectorExpansion.factor, map_prod, apply_ite, map_sub, map_one]

open Aeneas Aeneas.Std
open AspisR1SelectedMaskProbe
open AspisR1.ExtractedMaskQmPackBase4Semantic

def mappedPoint (point : Array field.QM31 10#usize) : Nat → Wide :=
  fun i => f (AspisR1.SelectorAtPointModel.exactPoint point i)

theorem pointSelector_maps_to_lifted_point (point : Array field.QM31 10#usize)
    (row : Fin 1024) :
    f (AspisR1.SelectorValueLaneModelComposition.pointSelector point row) =
      AspisV8.SelectedSelectorExpansion.tensorProduct (mappedPoint point) 10 row.val := by
  exact map_tensor f (AspisR1.SelectorAtPointModel.exactPoint point) 10 row.val

#print axioms map_tensor
#print axioms pointSelector_maps_to_lifted_point
end
end AspisR1.SelectorFieldTransport
