import BatchedWeightsCallerGlobalRangeBridgeV7
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace BatchedWeightsCallerNaturalIndexV1
open BatchedWeightsCallerGlobalRangeBridgeV1
open BatchedWeightsCallerRangeTraversalV1
open BatchedWeightsCallerSafeCadenceV4
abbrev BW := BatchedWeightsCallerRangeTraversalV1.BW
abbrev Usize := BatchedWeightsCallerRangeTraversalV1.Usize
abbrev Q := BatchedWeightsCallerRangeTraversalV1.Q
abbrev M := BatchedWeightsCallerRangeTraversalV1.M

def rangeIndexAt (i : Nat) : Usize :=
  UScalar.ofNatCore (i % 2^UScalarTy.Usize.numBits)
    (Nat.mod_lt i (by exact Nat.pow_pos (by omega : 0 < 2)))

theorem rangeIndexAt_val (n i : Nat) (hn : n < 2^UScalarTy.Usize.numBits) (hi : i < n) :
    (rangeIndexAt i).val = i := by
  simp only [rangeIndexAt, UScalar.ofNatCore_val_eq]
  exact Nat.mod_eq_of_lt (by omega)

theorem natural_range_safeRows
    (n : Nat) (state : BW) (hn : n < 2^UScalarTy.Usize.numBits)
    (powerAt : Nat → Q) (basisAt : Nat → M)
    (hlen : n ≤ state.raw.val.length)
    (hraw : GlobalRawPhaseBound state)
    (hpower0a : ∀ i, i < n → (powerAt i).c0.a.val < AspisV8R17.RawReducer.P)
    (hpower0b : ∀ i, i < n → (powerAt i).c0.b.val < AspisV8R17.RawReducer.P)
    (hpower1a : ∀ i, i < n → (powerAt i).c1.a.val < AspisV8R17.RawReducer.P)
    (hpower1b : ∀ i, i < n → (powerAt i).c1.b.val < AspisV8R17.RawReducer.P)
    (hbasis : ∀ i, i < n → (basisAt i).val < AspisV8R17.RawReducer.P) :
    ∃ final, SafeRows (rangeVisits n rangeIndexAt powerAt basisAt) state final := by
  apply rangeVisits_safeRows_of_global_phase_bound n state rangeIndexAt
    powerAt basisAt hlen
  · intro i hi
    exact rangeIndexAt_val n i hn hi
  · exact hraw
  · exact hpower0a
  · exact hpower0b
  · exact hpower1a
  · exact hpower1b
  · exact hbasis

#print axioms rangeIndexAt_val
#print axioms natural_range_safeRows
end BatchedWeightsCallerNaturalIndexV1
