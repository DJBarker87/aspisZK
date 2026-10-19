import BatchedWeightsCallerNaturalIndexV5
import BatchedWeightsSafeRowsPhaseV2
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace BatchedWeightsNaturalRangeQueryGlobalV1
open BatchedWeightsCallerNaturalIndexV1
open BatchedWeightsCallerRangeTraversalV1
open BatchedWeightsCallerSafeCadenceV4
open BatchedWeightsCallerGlobalRangeBridgeV1
open BatchedWeightsSafeRowsPhaseV1

abbrev BW := BatchedWeightsCallerSafeCadenceV4.BW
abbrev Usize := UScalar UScalarTy.Usize
abbrev Q := BatchedWeightsCallerSafeCadenceV4.Q
abbrev M := BatchedWeightsCallerSafeCadenceV4.M

private theorem add_ok_val (a b c : Usize) (h : a + b = Result.ok c) :
    c.val = a.val + b.val := by
  have he := UScalar.add_equiv a b
  rw [h] at he
  exact he.2.1

theorem rangeVisits_indices_eq_range
    (n : Nat) (indexAt : Nat → Usize) (powerAt : Nat → Q) (basisAt : Nat → M)
    (hindex : ∀ i, i < n → (indexAt i).val = i) :
    (rangeVisits n indexAt powerAt basisAt).map (fun v => v.index.val) = List.range n := by
  unfold rangeVisits
  rw [List.map_map]
  conv_rhs => rw [← List.map_id (List.range n)]
  apply List.map_congr_left
  intro i hi
  exact hindex i (List.mem_range.mp hi)

/-- An actual ascending source range of row pushes preserves a global
phase bound. Every row is selected exactly once; after the single checked
counter increment, the generated phase bound is uniform across the whole
raw vector. The caller-specific operand and initial global-bound facts remain
explicit inputs. -/
theorem natural_range_query_global
    (n : Nat) (state : BW)
    (hn : n < 2^UScalarTy.Usize.numBits)
    (hlen : n = state.raw.val.length)
    (hglobal : GlobalRawPhaseBound state)
    (powerAt : Nat → Q) (basisAt : Nat → M)
    (hpower0a : ∀ i, i < n → (powerAt i).c0.a.val < AspisV8R17.RawReducer.P)
    (hpower0b : ∀ i, i < n → (powerAt i).c0.b.val < AspisV8R17.RawReducer.P)
    (hpower1a : ∀ i, i < n → (powerAt i).c1.a.val < AspisV8R17.RawReducer.P)
    (hpower1b : ∀ i, i < n → (powerAt i).c1.b.val < AspisV8R17.RawReducer.P)
    (hbasis : ∀ i, i < n → (basisAt i).val < AspisV8R17.RawReducer.P)
    (hinc : ∃ nextTerms : Usize,
      (state.terms + 1#usize : Result Usize) = Result.ok nextTerms) :
    ∃ final, queryStep (rangeVisits n rangeIndexAt powerAt basisAt) state = Result.ok final ∧
      GlobalRawPhaseBound final ∧
      final.raw.val.length = state.raw.val.length ∧
      final.terms.val = state.terms.val + 1 := by
  have hlenLe : n ≤ state.raw.val.length := by omega
  obtain ⟨mid, hsafe⟩ := natural_range_safeRows n state hn powerAt basisAt hlenLe
    hglobal hpower0a hpower0b hpower1a hpower1b hbasis
  obtain ⟨nextTerms, hinc⟩ := hinc
  have hsafeActual := safeRows_actual _ state mid hsafe
  have hterms := safeRows_terms _ state mid hsafe
  have htermsVal : mid.terms.val = state.terms.val := congrArg UScalar.val hterms
  have hincVal : nextTerms.val = state.terms.val + 1 := by
    have hadd := add_ok_val state.terms 1#usize nextTerms hinc
    simpa using hadd
  have hquery : queryStep (rangeVisits n rangeIndexAt powerAt basisAt) state =
      Result.ok { mid with terms := nextTerms } := by
    simp [queryStep, incrementTerms, hsafeActual, hterms, hinc]
  have hmidlen : mid.raw.length = state.raw.length :=
    BatchedWeightsSafeRowsFrameV1.safeRows_length _ state mid hsafe
  change mid.raw.val.length = state.raw.val.length at hmidlen
  refine ⟨{ mid with terms := nextTerms }, hquery, ?_, ?_, ?_⟩
  intro index hindex k hk
  have hindexMid : index.val < mid.raw.val.length := by
    change index.val < mid.raw.val.length at hindex
    exact hindex
  have hindexState : index.val < state.raw.val.length := by
    rw [← hmidlen]
    exact hindexMid
  have hindexlt : index.val < n := by rw [hlen]; exact hindexState
  have hmem : index.val ∈ (rangeVisits n rangeIndexAt powerAt basisAt).map
      (fun v => v.index.val) := by
    rw [rangeVisits_indices_eq_range n rangeIndexAt powerAt basisAt
      (rangeIndexAt_val n · hn ·)]
    exact List.mem_range.mpr hindexlt
  have hmember := safeRows_member_next_phase_bound _ state mid index hindexState hsafe
    (rangeVisits_indices_nodup n rangeIndexAt powerAt basisAt (rangeIndexAt_val n · hn ·)) hmem k hk
  change AspisR1BatchedWeightsPushLoopAllPrefixV11.cellAt mid index hindex k hk <
      2^34 + ((state.terms.val + 1) % 4) * AspisR1BatchedAllPrefix.cap at hmember
  have htermsNext : ({ mid with terms := nextTerms } : BW).terms.val = state.terms.val + 1 := by
    change nextTerms.val = state.terms.val + 1
    exact hincVal
  change AspisR1BatchedWeightsPushLoopGlobalFrameV1.cellAt
      { mid with terms := nextTerms } index hindex k hk <
      2^34 + ({ mid with terms := nextTerms } : BW).terms.val % 4 * AspisR1BatchedAllPrefix.cap
  rw [htermsNext]
  exact hmember
  · change mid.raw.val.length = state.raw.val.length
    exact hmidlen
  · exact hincVal

#print axioms natural_range_query_global
end BatchedWeightsNaturalRangeQueryGlobalV1
