import BatchedWeightsPushOuterFlushV15
import BatchedWeightsFlushLaneV8
import BatchedWeightsFlushPrimitiveV2
import BatchedWeightsFlushLaneBoundsV3
import BatchedWeightsPushLoopFlushInputBoundV4
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace BatchedWeightsSelectedFlushBoundV1
open AspisR1BatchedWeightsExtraction
open AspisR1BatchedWeightsPushLoopAllPrefixV11
abbrev BW := batched_weights.BatchedWeights
abbrev Usize := UScalar UScalarTy.Usize
abbrev M := aspis_core.field.M31
abbrev Q := aspis_core.field.QM31

/-- At the flush boundary, the actual outer generated push replaces the
selected four-limb row by its four folded values, each below 2^34. -/
theorem selected_flush_cell_reset
    (index : Usize) (initial out : BW) (power : Q) (basis : M)
    (hindex : index.val < initial.raw.length)
    (hraw : ∀ k : Usize, ∀ hk : k.val < 4,
      cellAt initial index hindex k hk <
        2^34 + (initial.terms.val % 4) * AspisR1BatchedAllPrefix.cap)
    (ha : power.c0.a.val < AspisV8R17.RawReducer.P)
    (hb : power.c0.b.val < AspisV8R17.RawReducer.P)
    (hc : power.c1.a.val < AspisV8R17.RawReducer.P)
    (hd : power.c1.b.val < AspisV8R17.RawReducer.P)
    (hbasis : basis.val < AspisV8R17.RawReducer.P)
    (hflush : initial.terms.val % 4 = 3)
    (hpush : batched_weights.BatchedWeights.push initial index power basis = .ok out) :
    ∃ hout : index.val < out.raw.length,
      ∀ k : Usize, ∀ hk : k.val < 4, cellAt out index hout k hk < 2^34 := by
  obtain ⟨mid,lane,newLane,old,back,x0,x1,x2,x3,y0,y1,y2,y3,
      hloop,hvec,hflushLane,hmut,hback,houter,hterms,hpost,
      hy0,hy1,hy2,hy3,hyv0,hyv1,hyv2,hyv3⟩ :=
    BatchedWeightsPushOuterFlushV15.push_flush_success_with_bounds_and_back
      index initial power basis hindex hraw ha hb hc hd hbasis hflush
  have houtEq : out = { mid with raw := back newLane } := Result.ok.inj (hpush.symm.trans houter)
  subst out
  have hmIndex : index.val < mid.raw.length := hpost.2.1
  obtain ⟨laneOut,hlaneOut,hlaneBounds⟩ :=
    BatchedWeightsFlushLaneBoundsV1.flushLane_result_bounds lane
  have hnew : newLane = laneOut := Result.ok.inj (hflushLane.symm.trans hlaneOut)
  have hlen : (back newLane).length = mid.raw.length := by
    simp [hback, alloc.vec.Vec.set, List.length_set]
  have houtIndex : index.val < (back newLane).length := by rw [hlen]; exact hmIndex
  refine ⟨houtIndex, ?_⟩
  intro k hk
  have hcell : cellAt { mid with raw := back newLane } index houtIndex k hk =
      (newLane.val[k.val]'(by simpa [newLane.property] using hk)).val := by
    simp [cellAt, rowAt, hback, alloc.vec.Vec.set, List.getElem_set_self]
  rw [hcell, hnew]
  exact hlaneBounds k hk

#print axioms selected_flush_cell_reset
end BatchedWeightsSelectedFlushBoundV1
