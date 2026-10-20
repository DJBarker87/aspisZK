import BatchedWeightsPushOuterFlushV13
import BatchedWeightsPushOuterNoFlushV3

/-! Totality of the actual extracted outer rho push, for both flush phases.
The selected row invariant, index bound and canonical operands remain explicit
caller premises. This function deliberately leaves the global counter alone. -/
set_option autoImplicit false
namespace AspisR1.R22BatchedPushTotal
open Aeneas Aeneas.Std Result
open AspisR1BatchedWeightsExtraction AspisR1BatchedWeightsPushLoopAllPrefixV11
abbrev BW := batched_weights.BatchedWeights
abbrev Q := aspis_core.field.QM31
abbrev M := aspis_core.field.M31

theorem push_total
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
    ∃ out : BW, batched_weights.BatchedWeights.push initial index power basis = .ok out ∧
      out.terms = initial.terms := by
  by_cases hflush : initial.terms.val % 4 = 3
  · obtain ⟨mid, lane, newLane, old, back, _, _, _, _, hrun, hterms⟩ :=
      BatchedWeightsPushOuterFlushV13.push_flush_success index initial power basis
        hindex hraw ha hb hc hd hbasis hflush
    exact ⟨_, hrun, hterms⟩
  · obtain ⟨mid, _, hrun, hterms⟩ :=
      BatchedWeightsPushOuterNoFlushV3.push_nonflush_success index initial power basis
        hindex hraw ha hb hc hd hbasis hflush
    exact ⟨mid, hrun, hterms⟩

#print axioms push_total
end AspisR1.R22BatchedPushTotal
