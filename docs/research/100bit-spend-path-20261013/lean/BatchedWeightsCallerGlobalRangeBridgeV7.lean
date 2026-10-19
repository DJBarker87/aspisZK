import BatchedWeightsCallerRangeTraversalV7
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace BatchedWeightsCallerGlobalRangeBridgeV1
open BatchedWeightsCallerRangeTraversalV1
open BatchedWeightsCallerSafeCadenceV4
abbrev BW := BatchedWeightsCallerRangeTraversalV1.BW
abbrev Usize := BatchedWeightsCallerRangeTraversalV1.Usize
abbrev Q := BatchedWeightsCallerRangeTraversalV1.Q
abbrev M := BatchedWeightsCallerRangeTraversalV1.M

/-- One phase-wide bound over every existing raw row and all four coordinates. -/
def GlobalRawPhaseBound (state : BW) : Prop :=
  ∀ (index : Usize) (hindex : index.val < state.raw.val.length),
    ∀ k : Usize, ∀ hk : k.val < 4,
      AspisR1BatchedWeightsPushLoopGlobalFrameV1.cellAt state index hindex k hk <
        2^34 + state.terms.val % 4 * AspisR1BatchedAllPrefix.cap

/-- An ascending row traversal is safe from a single global phase bound, when
its indices enumerate `0..n-1` and each source operand is canonical. -/
theorem rangeVisits_safeRows_of_global_phase_bound
    (n : Nat) (state : BW) (indexAt : Nat → Usize)
    (powerAt : Nat → Q) (basisAt : Nat → M)
    (hlen : n ≤ state.raw.val.length)
    (hindex : ∀ i, i < n → (indexAt i).val = i)
    (hraw : GlobalRawPhaseBound state)
    (hpower0a : ∀ i, i < n → (powerAt i).c0.a.val < AspisV8R17.RawReducer.P)
    (hpower0b : ∀ i, i < n → (powerAt i).c0.b.val < AspisV8R17.RawReducer.P)
    (hpower1a : ∀ i, i < n → (powerAt i).c1.a.val < AspisV8R17.RawReducer.P)
    (hpower1b : ∀ i, i < n → (powerAt i).c1.b.val < AspisV8R17.RawReducer.P)
    (hbasis : ∀ i, i < n → (basisAt i).val < AspisV8R17.RawReducer.P) :
    ∃ final, SafeRows (rangeVisits n indexAt powerAt basisAt) state final := by
  apply rangeVisits_safeRows n state indexAt powerAt basisAt hlen hindex
  · intro i hi k hk
    have hvalid : (indexAt i).val < state.raw.val.length := by
      rw [hindex i hi]
      exact Nat.lt_of_lt_of_le hi hlen
    exact hraw (indexAt i) hvalid k hk
  · exact hpower0a
  · exact hpower0b
  · exact hpower1a
  · exact hpower1b
  · exact hbasis

#print axioms rangeVisits_safeRows_of_global_phase_bound
end BatchedWeightsCallerGlobalRangeBridgeV1
