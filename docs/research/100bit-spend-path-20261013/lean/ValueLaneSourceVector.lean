import ValueLaneIntervalJoin

/-! The two actual source packing calls compute one contiguous 35-cell
value-family contribution. The source-selected QM31 lanes are identified
with zero-padded vectors after the existing exact field embedding. -/
set_option autoImplicit false
namespace AspisR1.ValueLaneSourceVector
noncomputable section
open Aeneas Aeneas.Std Result
open AspisR1.PreweightedClosureSuccess
open AspisR1.PreweightedGroupUpdate
open AspisR1.PreweightedLoopModel
open AspisR1.ExtractedMaskQmPackBase4Semantic
open AspisR1.ValueLaneIntervalJoin

def arrayVector {N : Usize} (a : Array QM N) : Fin N.val → Wide :=
  fun i => f (AspisR1.ExtractedMaskQM31Exact.decode
    (a.val[i.val]'(by simpa [a.property] using i.isLt)))

theorem selectedCell_vector {N : Usize} (a : Array QM N)
    (start group slot : Nat) :
    f (AspisR1.ExtractedMaskQM31Exact.decode (selectedCell a start group slot)) =
      selectVector start (arrayVector a) (4*group+slot) := by
  by_cases h : start ≤ 4*group+slot ∧ 4*group+slot < start+N.val
  · have hb : 4*group+slot-start < N.val := by omega
    simp only [selectedCell, if_pos h, sourceCell, dif_pos hb,
      selectVector, dif_pos h, arrayVector]
  · simp only [selectedCell, if_neg h, selectVector, dif_neg h,
      AspisR1.ExtractedMaskConstants.zero_decode, map_zero]

theorem run_contiguous (packed : Array QM 24#usize) (range : Array QM 33#usize)
    (conservation : Array QM 2#usize)
    (hpacked : CanonicalArray packed) (hrange : CanonicalArray range)
    (hconservation : CanonicalArray conservation) :
    ∃ out : Array QM 24#usize,
      AspisR1.ValueLanePackedComposition.run packed range conservation = .ok out ∧
      CanonicalArray out ∧
      ∀ j : Fin 24,
        f (decoded out j) = f (decoded packed j) +
          R0P.pack4 PackB (fun k : Fin 4 =>
            selectVector 49 (appendVector (arrayVector range)
              (arrayVector conservation)) (4*j.val+k.val)) := by
  obtain ⟨packed1, out, hfirst, hsecond, hrun, hcanon, hmodel⟩ :=
    AspisR1.ValueLanePackedComposition.run_semantic
      packed range conservation hpacked hrange hconservation
  refine ⟨out, hrun, hcanon, ?_⟩
  intro j
  rw [hmodel]
  congr 1
  congr 1
  funext k
  rw [selectedCell_vector, selectedCell_vector, selectVector_append]
  have hstart : 49 + (33#usize).val = 82 := by scalar_tac
  rw [hstart]

#print axioms selectedCell_vector
#print axioms run_contiguous
end
end AspisR1.ValueLaneSourceVector
