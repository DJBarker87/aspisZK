import BatchedWeightsSelectedPushFrameV5
import BatchedWeightsPushOuterNoFlushV3
import BatchedWeightsPushLoopGlobalFrameV1
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace BatchedWeightsSelectedPushGeneralFrameV1
open AspisR1BatchedWeightsExtraction
open BatchedWeightsSelectedPushFrameV5
open BatchedWeightsPushOuterNoFlushV3
open AspisR1BatchedWeightsPushLoopGlobalFrameV1
abbrev BW := AspisR1BatchedWeightsPushLoopAllPrefixV11.BW
abbrev Usize := UScalar UScalarTy.Usize
abbrev M := AspisR1BatchedWeightsPushLoopAllPrefixV11.M
abbrev Q := AspisR1BatchedWeightsPushLoopAllPrefixV11.Q
abbrev Range := core.ops.range.Range Usize

theorem selected_push_preserves_outer_frame
    (index : Usize) (initial : BW) (power : Q) (basis : M)
    (hindex : index.val < initial.raw.length)
    (hraw : ∀ k : Usize, ∀ hk : k.val < 4,
      cellAt initial index hindex k hk <
        2^34 + (initial.terms.val % 4) * AspisR1BatchedAllPrefix.cap)
    (ha : power.c0.a.val < AspisV8R17.RawReducer.P)
    (hb : power.c0.b.val < AspisV8R17.RawReducer.P)
    (hc : power.c1.a.val < AspisV8R17.RawReducer.P)
    (hd : power.c1.b.val < AspisV8R17.RawReducer.P)
    (hbasis : basis.val < AspisV8R17.RawReducer.P) :
    ∃ out : BW,
      batched_weights.BatchedWeights.push initial index power basis = .ok out ∧
      out.terms = initial.terms ∧
      out.raw.val.length = initial.raw.val.length ∧
      ∀ hlen : out.raw.val.length = initial.raw.val.length,
      ∀ k : Usize, ∀ hk : k.val < initial.raw.length,
        k.val ≠ index.val →
        out.raw.val[k.val]'(by change k.val < out.raw.val.length; rw [hlen]; exact hk) =
          initial.raw.val[k.val]'hk := by
  by_cases hflush : initial.terms.val % 4 = 3
  · obtain ⟨out,hpush,hterms,hlen,hframe⟩ :=
      BatchedWeightsSelectedPushFrameV5.selected_push_frame
        index initial power basis hindex hraw ha hb hc hd hbasis hflush
    exact ⟨out,hpush,hterms,hlen,hframe⟩
  · obtain ⟨mid,hloop,hpush,hterms⟩ :=
      BatchedWeightsPushOuterNoFlushV3.push_nonflush_success
        index initial power basis hindex hraw ha hb hc hd hbasis hflush
    obtain ⟨midG,hloopG,hpostG⟩ :=
      AspisR1BatchedWeightsPushLoopGlobalFrameV1.push_loop_all_prefix
        index initial power basis hindex hraw ha hb hc hd hbasis
    have hloopG' : batched_weights.BatchedWeights.push_loop
        ({ start := 0#usize, «end» := 4#usize } : Range)
        initial index basis
        (Array.make 4#usize [power.c0.a,power.c0.b,power.c1.a,power.c1.b]) = .ok midG := by
      simpa [BatchedWeightsPushLoopFlushInputBoundV4.limbsOf] using hloopG
    have hmidEq : midG = mid := Result.ok.inj (hloopG'.symm.trans hloop)
    subst midG
    rcases hpostG with ⟨htermsG, ⟨hindexG,hcells,hlenG,hframeG⟩⟩
    have hterms' : mid.terms = initial.terms := hterms
    refine ⟨mid,hpush,hterms',hlenG,?_⟩
    intro hlen k hk hne
    exact hframeG hlen k hk hne

#print axioms selected_push_preserves_outer_frame
end BatchedWeightsSelectedPushGeneralFrameV1
