import BatchedWeightsFlushLaneV8
import AspisR1BatchedFoldSourceStep
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace BatchedWeightsFlushLaneBoundsV1
open AspisR1BatchedWeightsExtraction
abbrev Usize := UScalar UScalarTy.Usize
abbrev U64 := UScalar UScalarTy.U64
abbrev Lane := Array U64 4#usize

private theorem array_index_usize_ok {α : Type} {n : Usize}
    (a : Array α n) (i : Usize) (hi : i.val < n.val) :
    Array.index_usize a i = .ok (a.val[i.val]'(by simpa [a.property] using hi)) := by
  have hidx : i.val < a.val.length := by simpa [a.property] using hi
  unfold Array.index_usize
  change (match a.val[i.val]? with
    | none => Result.fail Error.arrayOutOfBounds
    | some x => Result.ok x) = Result.ok (a.val[i.val]'hidx)
  rw [List.getElem?_eq_getElem hidx]

/-- The generated four-coordinate lane flush returns a literal four-element
array whose every coordinate is in the reduced 34-bit range. -/
theorem flushLane_result_bounds (lane : Lane) :
    ∃ out : Lane, BatchedWeightsFlushLaneV8.flushLane lane = .ok out ∧
      ∀ k : Usize, ∀ hk : k.val < 4,
        (out.val[k.val]'(by simpa [out.property] using hk)).val < 2^34 := by
  have h0 : (0#usize).val < lane.length := by simpa [lane.property]
  have h1 : (1#usize).val < lane.length := by simpa [lane.property]
  have h2 : (2#usize).val < lane.length := by simpa [lane.property]
  have h3 : (3#usize).val < lane.length := by simpa [lane.property]
  obtain ⟨x0,hx0,_⟩ := WP.spec_imp_exists (Array.index_usize_spec lane 0#usize h0)
  obtain ⟨x1,hx1,_⟩ := WP.spec_imp_exists (Array.index_usize_spec lane 1#usize h1)
  obtain ⟨x2,hx2,_⟩ := WP.spec_imp_exists (Array.index_usize_spec lane 2#usize h2)
  obtain ⟨x3,hx3,_⟩ := WP.spec_imp_exists (Array.index_usize_spec lane 3#usize h3)
  obtain ⟨y0,y1,y2,y3,hy0,hy1,hy2,hy3,hyv0,hyv1,hyv2,hyv3,hout⟩ :=
    BatchedWeightsFlushLaneV8.flushLane_success lane x0 x1 x2 x3 hx0 hx1 hx2 hx3
  have hx0b : x0.val < 2^64 := by
    simpa [UScalarTy.U64_numBits_eq] using x0.bv.isLt
  have hx1b : x1.val < 2^64 := by
    simpa [UScalarTy.U64_numBits_eq] using x1.bv.isLt
  have hx2b : x2.val < 2^64 := by
    simpa [UScalarTy.U64_numBits_eq] using x2.bv.isLt
  have hx3b : x3.val < 2^64 := by
    simpa [UScalarTy.U64_numBits_eq] using x3.bv.isLt
  have hb0 : y0.val < 2^34 := by
    rw [hyv0]
    exact AspisR1BatchedFoldSourceStep.fold_lt_two34 hx0b
  have hb1 : y1.val < 2^34 := by
    rw [hyv1]
    exact AspisR1BatchedFoldSourceStep.fold_lt_two34 hx1b
  have hb2 : y2.val < 2^34 := by
    rw [hyv2]
    exact AspisR1BatchedFoldSourceStep.fold_lt_two34 hx2b
  have hb3 : y3.val < 2^34 := by
    rw [hyv3]
    exact AspisR1BatchedFoldSourceStep.fold_lt_two34 hx3b
  refine ⟨Array.make 4#usize [y0,y1,y2,y3], hout, ?_⟩
  intro k hk
  have hc : k.val = 0 ∨ k.val = 1 ∨ k.val = 2 ∨ k.val = 3 := by omega
  rcases hc with h | h | h | h
  · have hk0 : k = 0#usize := UScalar.eq_of_val_eq h
    subst k
    simpa [Array.make] using hb0
  · have hk1 : k = 1#usize := UScalar.eq_of_val_eq h
    subst k
    simpa [Array.make] using hb1
  · have hk2 : k = 2#usize := UScalar.eq_of_val_eq h
    subst k
    simpa [Array.make] using hb2
  · have hk3 : k = 3#usize := UScalar.eq_of_val_eq h
    subst k
    simpa [Array.make] using hb3

#print axioms flushLane_result_bounds
end BatchedWeightsFlushLaneBoundsV1
