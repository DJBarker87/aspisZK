import ValueLaneSourceVector
import R0P.Value

/-! List-form interface for the source value-family packing result. This
matches the retained semantic model's residual-list representation, including
zero padding outside the full 35-cell interval. -/
set_option autoImplicit false
namespace AspisR1.ValueLaneResidualList
noncomputable section
open Aeneas Aeneas.Std Result
open AspisR1.PreweightedClosureSuccess
open AspisR1.PreweightedGroupUpdate
open AspisR1.PreweightedLoopModel
open AspisR1.ExtractedMaskQmPackBase4Semantic
open AspisR1.ValueLaneIntervalJoin
open AspisR1.ValueLaneSourceVector

theorem ofFn_appendVector {K : Type} {n m : Nat} (a : Fin n → K) (b : Fin m → K) :
    List.ofFn (appendVector a b) = List.ofFn a ++ List.ofFn b := by
  rw [List.ofFn_add]
  congr 1
  · congr 1
    funext i
    simp [appendVector, i.isLt]
  · congr 1
    funext i
    simp [appendVector]

def selectList {K : Type} [Zero K] (start : Nat) (xs : List K) (index : Nat) : K :=
  if h : start ≤ index ∧ index < start+xs.length then xs[index-start]'(by omega)
  else 0

theorem selectList_ofFn {K : Type} [Zero K] {n : Nat}
    (start index : Nat) (a : Fin n → K) :
    selectList start (List.ofFn a) index = selectVector start a index := by
  unfold selectList selectVector
  simp only [List.length_ofFn]
  split
  · simp only [List.getElem_ofFn]
  · rfl

def sourceResiduals (range : Array QM 33#usize) (conservation : Array QM 2#usize) :
    List Wide := List.ofFn (arrayVector range) ++ List.ofFn (arrayVector conservation)

theorem run_residuals (packed : Array QM 24#usize) (range : Array QM 33#usize)
    (conservation : Array QM 2#usize)
    (hpacked : CanonicalArray packed) (hrange : CanonicalArray range)
    (hconservation : CanonicalArray conservation) :
    ∃ out : Array QM 24#usize,
      AspisR1.ValueLanePackedComposition.run packed range conservation = .ok out ∧
      CanonicalArray out ∧
      ∀ j : Fin 24,
        f (decoded out j) = f (decoded packed j) +
          R0P.pack4 PackB (fun k : Fin 4 =>
            selectList 49 (sourceResiduals range conservation) (4*j.val+k.val)) := by
  obtain ⟨out, hrun, hcanon, hmodel⟩ :=
    run_contiguous packed range conservation hpacked hrange hconservation
  refine ⟨out, hrun, hcanon, ?_⟩
  intro j
  rw [hmodel]
  congr 1
  congr 1
  funext k
  rw [sourceResiduals, ← ofFn_appendVector, selectList_ofFn]

/-- The remaining residual identification is explicit: after it is supplied
by the source construction proof, no packing or success hypothesis remains. -/
theorem run_valueFamily (packed : Array QM 24#usize) (range : Array QM 33#usize)
    (conservation : Array QM 2#usize)
    (pub : R0P.Public Wide) (o : R0P.Openings Wide) (sel : R0P.Sel Wide)
    (hpacked : CanonicalArray packed) (hrange : CanonicalArray range)
    (hconservation : CanonicalArray conservation)
    (hresiduals : sourceResiduals range conservation =
      (R0P.valueFamily (K := Wide)).residuals pub o sel) :
    ∃ out : Array QM 24#usize,
      AspisR1.ValueLanePackedComposition.run packed range conservation = .ok out ∧
      CanonicalArray out ∧
      ∀ j : Fin 24,
        f (decoded out j) = f (decoded packed j) +
          R0P.pack4 PackB (fun k : Fin 4 =>
            selectList 49 ((R0P.valueFamily (K := Wide)).residuals pub o sel)
              (4*j.val+k.val)) := by
  obtain ⟨out, hrun, hcanon, hmodel⟩ :=
    run_residuals packed range conservation hpacked hrange hconservation
  exact ⟨out, hrun, hcanon, by simpa only [hresiduals] using hmodel⟩

#print axioms ofFn_appendVector
#print axioms selectList_ofFn
#print axioms run_residuals
#print axioms run_valueFamily
end
end AspisR1.ValueLaneResidualList
