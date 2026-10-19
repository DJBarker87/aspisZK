import BatchedWeightsSelectedPhaseBoundV9
import BatchedWeightsSelectedFlushBoundV6
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace BatchedWeightsSelectedPhaseBoundV10
open AspisR1BatchedWeightsExtraction
abbrev BW := BatchedWeightsSelectedPhaseBoundV1.BW
abbrev Usize := BatchedWeightsSelectedPhaseBoundV1.Usize
abbrev M := BatchedWeightsSelectedPhaseBoundV1.M
abbrev Q := BatchedWeightsSelectedPhaseBoundV1.Q

/-- The actual generated `push` advances every selected cell to the next
phase envelope; its phase-three branch performs the canonical 34-bit flush. -/
theorem selected_cell_next_phase_bound
    (index : Usize) (initial out : BW) (power : Q) (basis : M)
    (hindex : index.val < initial.raw.length)
    (hraw : ∀ k : Usize, ∀ hk : k.val < 4,
      AspisR1BatchedWeightsPushLoopAllPrefixV11.cellAt initial index hindex k hk <
        2^34 + (initial.terms.val % 4) * AspisR1BatchedAllPrefix.cap)
    (ha : power.c0.a.val < AspisV8R17.RawReducer.P)
    (hb : power.c0.b.val < AspisV8R17.RawReducer.P)
    (hc : power.c1.a.val < AspisV8R17.RawReducer.P)
    (hd : power.c1.b.val < AspisV8R17.RawReducer.P)
    (hbasis : basis.val < AspisV8R17.RawReducer.P)
    (hpush : batched_weights.BatchedWeights.push initial index power basis = .ok out) :
    ∃ hout : index.val < out.raw.length,
      ∀ k : Usize, ∀ hk : k.val < 4,
        AspisR1BatchedWeightsPushLoopAllPrefixV11.cellAt out index hout k hk <
          2^34 + ((initial.terms.val + 1) % 4) * AspisR1BatchedAllPrefix.cap := by
  by_cases hphase : initial.terms.val % 4 = 3
  · obtain ⟨hout,hbound⟩ :=
      BatchedWeightsSelectedFlushBoundV1.selected_flush_cell_reset index initial out power basis
        hindex hraw ha hb hc hd hbasis hphase hpush
    have hnext : (initial.terms.val + 1) % 4 = 0 := by omega
    refine ⟨hout, ?_⟩
    intro k hk
    rw [hnext]
    exact hbound k hk
  · have hlt : initial.terms.val % 4 < 3 := by omega
    exact BatchedWeightsSelectedPhaseBoundV1.selected_nonflush_cell_next_bound
      index initial out power basis hindex hraw ha hb hc hd hbasis hlt hpush

#print axioms selected_cell_next_phase_bound
end BatchedWeightsSelectedPhaseBoundV10
