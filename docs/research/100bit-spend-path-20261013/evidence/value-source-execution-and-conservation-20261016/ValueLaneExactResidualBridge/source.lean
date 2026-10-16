import ValueLaneResidualList
import ValueFamilyFieldTransport

/-! Instantiation of the packed source result from exact-QM31 residual
identification. The only remaining semantic premise concerns the source's
constructed residuals, not successful packing or field transport. -/
set_option autoImplicit false
namespace AspisR1.ValueLaneExactResidualBridge
noncomputable section
open Aeneas Aeneas.Std Result
open AspisR1.PreweightedClosureSuccess
open AspisR1.PreweightedGroupUpdate
open AspisR1.PreweightedLoopModel
open AspisR1.ExtractedMaskQmPackBase4Semantic
open AspisR1.ValueLaneSourceVector
open AspisR1.ValueLaneResidualList
open AspisR1.ValueFamilyFieldTransport

abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact

def exactVector {N : Usize} (a : Array QM N) : Fin N.val → ExactQM :=
  fun i => AspisR1.ExtractedMaskQM31Exact.decode
    (a.val[i.val]'(by simpa [a.property] using i.isLt))

def exactResiduals (range : Array QM 33#usize) (conservation : Array QM 2#usize) :
    List ExactQM := List.ofFn (exactVector range) ++ List.ofFn (exactVector conservation)

theorem arrayVector_list (N : Usize) (a : Array QM N) :
    List.ofFn (arrayVector a) = (List.ofFn (exactVector a)).map f := by
  rw [List.map_ofFn]
  rfl

theorem residuals_map (range : Array QM 33#usize) (conservation : Array QM 2#usize) :
    sourceResiduals range conservation = (exactResiduals range conservation).map f := by
  simp only [sourceResiduals, exactResiduals, List.map_append, arrayVector_list]

theorem residuals_valueFamily (range : Array QM 33#usize)
    (conservation : Array QM 2#usize)
    (pub : R0P.Public ExactQM) (pub' : R0P.Public Wide)
    (o : R0P.Openings ExactQM) (sel : R0P.Sel ExactQM)
    (hexact : exactResiduals range conservation =
      (R0P.valueFamily (K := ExactQM)).residuals pub o sel) :
    sourceResiduals range conservation =
      (R0P.valueFamily (K := Wide)).residuals pub' (mapOpenings f o)
        (fun i => f (sel i)) := by
  rw [residuals_map, hexact]
  exact map_family f pub pub' o sel

theorem run_exact_valueFamily (packed : Array QM 24#usize)
    (range : Array QM 33#usize) (conservation : Array QM 2#usize)
    (pub : R0P.Public ExactQM) (pub' : R0P.Public Wide)
    (o : R0P.Openings ExactQM) (sel : R0P.Sel ExactQM)
    (hpacked : CanonicalArray packed) (hrange : CanonicalArray range)
    (hconservation : CanonicalArray conservation)
    (hexact : exactResiduals range conservation =
      (R0P.valueFamily (K := ExactQM)).residuals pub o sel) :
    ∃ out : Array QM 24#usize,
      AspisR1.ValueLanePackedComposition.run packed range conservation = .ok out ∧
      CanonicalArray out ∧
      ∀ j : Fin 24,
        f (decoded out j) = f (decoded packed j) +
          R0P.pack4 PackB (fun k : Fin 4 =>
            selectList 49 ((R0P.valueFamily (K := Wide)).residuals pub'
              (mapOpenings f o) (fun i => f (sel i))) (4*j.val+k.val)) := by
  exact run_valueFamily packed range conservation pub' (mapOpenings f o)
    (fun i => f (sel i)) hpacked hrange hconservation
    (residuals_valueFamily range conservation pub pub' o sel hexact)

#print axioms arrayVector_list
#print axioms residuals_map
#print axioms residuals_valueFamily
#print axioms run_exact_valueFamily
end
end AspisR1.ValueLaneExactResidualBridge
