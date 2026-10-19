import BatchedWeightsPushOuterFlushV15
import BatchedWeightsPushLoopGlobalFrameV1
import BatchedWeightsPushOuterVecFrameV1
import BatchedWeightsPushLoopFlushInputBoundV4
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace BatchedWeightsSelectedPushFrameV5
open BatchedWeightsPushOuterFlushV15
open AspisR1BatchedWeightsExtraction
open AspisR1BatchedWeightsPushLoopGlobalFrameV1
abbrev BW := AspisR1BatchedWeightsPushLoopAllPrefixV11.BW
abbrev Usize := UScalar UScalarTy.Usize
abbrev M := AspisR1BatchedWeightsPushLoopAllPrefixV11.M
abbrev Q := AspisR1BatchedWeightsPushLoopAllPrefixV11.Q
abbrev Range := core.ops.range.Range Usize

/-- Actual generated selected-row push, with the outer Vec write frame made
explicit. The selected lane is changed by the actual flush; every other row
and the outer vector length are preserved. -/
theorem selected_push_frame
    (index : Usize) (initial : BW) (power : Q) (basis : M)
    (hindex : index.val < initial.raw.length)
    (hraw : ∀ k : Usize, ∀ hk : k.val < 4,
      cellAt initial index hindex k hk <
        2^34 + (initial.terms.val % 4) * AspisR1BatchedAllPrefix.cap)
    (ha : power.c0.a.val < AspisV8R17.RawReducer.P)
    (hb : power.c0.b.val < AspisV8R17.RawReducer.P)
    (hc : power.c1.a.val < AspisV8R17.RawReducer.P)
    (hd : power.c1.b.val < AspisV8R17.RawReducer.P)
    (hbasis : basis.val < AspisV8R17.RawReducer.P)
    (hflush : initial.terms.val % 4 = 3) :
    ∃ out : BW,
      batched_weights.BatchedWeights.push initial index power basis = .ok out ∧
      out.terms = initial.terms ∧
      out.raw.val.length = initial.raw.val.length ∧
      ∀ hlen : out.raw.val.length = initial.raw.val.length,
      ∀ k : Usize, ∀ hk : k.val < initial.raw.length,
        k.val ≠ index.val →
        out.raw.val[k.val]'(by change k.val < out.raw.val.length; rw [hlen]; exact hk) =
          initial.raw.val[k.val]'hk := by
  obtain ⟨mid,lane,newLane,old,back,x0,x1,x2,x3,y0,y1,y2,y3,
    hloop,hvec,hflushLane,hmut,hback,hpush,hterms,hpost,hl0,hl1,hl2,hl3,
    hm0,hm1,hm2,hm3⟩ :=
    BatchedWeightsPushOuterFlushV15.push_flush_success_with_bounds_and_back
      index initial power basis hindex hraw ha hb hc hd hbasis hflush
  obtain ⟨midG,hloopG,hglobal⟩ :=
    AspisR1BatchedWeightsPushLoopGlobalFrameV1.push_loop_all_prefix
      index initial power basis hindex hraw ha hb hc hd hbasis
  have hloopG' : batched_weights.BatchedWeights.push_loop
      ({ start := 0#usize, «end» := 4#usize } : Range)
      initial index basis
      (Array.make 4#usize [power.c0.a,power.c0.b,power.c1.a,power.c1.b]) = .ok midG := by
    simpa [BatchedWeightsPushLoopFlushInputBoundV4.limbsOf] using hloopG
  have hmidEq : midG = mid := Result.ok.inj (hloopG'.symm.trans hloop)
  subst midG
  rcases hglobal with ⟨_, ⟨hselectedIndex,hselected,hlenMid,hframeMid⟩⟩
  have hlenOut : (alloc.vec.Vec.set mid.raw index newLane).val.length = initial.raw.val.length := by
    simp [alloc.vec.Vec.set, List.length_set, hlenMid]
  have hframeOut : ∀ hlen : (alloc.vec.Vec.set mid.raw index newLane).val.length = initial.raw.val.length,
      ∀ k : Usize, ∀ hk : k.val < initial.raw.length,
      k.val ≠ index.val →
      (alloc.vec.Vec.set mid.raw index newLane).val[k.val]'(by change k.val < (alloc.vec.Vec.set mid.raw index newLane).val.length; rw [hlen]; exact hk) =
        initial.raw.val[k.val]'hk := by
    intro hlen k hk hne
    have hkMid : k.val < mid.raw.length := by rw [hlenMid]; exact hk
    have hset := BatchedWeightsPushOuterVecFrameV1.vec_set_preserves_length_and_other_rows
      mid.raw index k hselectedIndex hkMid hne newLane
    have hmid := hframeMid hlenMid k hk hne
    calc
      (alloc.vec.Vec.set mid.raw index newLane).val[k.val]'
        (by rw [hlen]; exact hk) = mid.raw.val[k.val]'hkMid := by
          exact hset.2
      _ = initial.raw.val[k.val]'hk := hmid
  have hpush' : batched_weights.BatchedWeights.push initial index power basis =
      .ok { mid with raw := alloc.vec.Vec.set mid.raw index newLane } := by
    simpa [hback] using hpush
  refine ⟨{ mid with raw := alloc.vec.Vec.set mid.raw index newLane }, hpush', ?_, ?_, ?_⟩
  · simpa using hterms
  · simpa [alloc.vec.Vec.set, List.length_set] using hlenMid
  · intro hlen k hk hne
    exact hframeOut (by simpa [alloc.vec.Vec.set, List.length_set] using hlenMid) k hk hne

#print axioms selected_push_frame
end BatchedWeightsSelectedPushFrameV5
