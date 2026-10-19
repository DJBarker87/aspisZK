import BatchedWeightsNaturalRangeQueryGlobalV1
import BatchedWeightsNewInitialGlobalBoundV6
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace BatchedWeightsNewQueryCallerV1
open AspisR1BatchedWeightsExtraction
open BatchedWeightsCallerGlobalRangeBridgeV1
open BatchedWeightsNaturalRangeQueryGlobalV1
open BatchedWeightsCallerSafeCadenceV4

/-- Source-caller composition: a successful `new` initializes every raw limb
below the phase-zero bound. If the caller's actual weight slice is at most 256
rows, its ascending query range has the exact allocated length and the existing
checked cadence theorem yields the post-query global phase bound. Operand
canonicality remains an explicit caller fact; the checked increment follows from
the constructor’s zero counter. -/
theorem successful_new_then_natural_query_global
    (weights : Slice aspis_core.field.QM31) (state : batched_weights.BatchedWeights)
    (hnew : batched_weights.BatchedWeights.new weights = .ok (.Ok state))
    (n : Nat) (hnlen : n = (Slice.len weights).val) (hmax : n ≤ 256)
    (powerAt : Nat → BatchedWeightsNaturalRangeQueryGlobalV1.Q)
    (basisAt : Nat → BatchedWeightsNaturalRangeQueryGlobalV1.M)
    (hpower0a : ∀ i, i < n → (powerAt i).c0.a.val < AspisV8R17.RawReducer.P)
    (hpower0b : ∀ i, i < n → (powerAt i).c0.b.val < AspisV8R17.RawReducer.P)
    (hpower1a : ∀ i, i < n → (powerAt i).c1.a.val < AspisV8R17.RawReducer.P)
    (hpower1b : ∀ i, i < n → (powerAt i).c1.b.val < AspisV8R17.RawReducer.P)
    (hbasis : ∀ i, i < n → (basisAt i).val < AspisV8R17.RawReducer.P)
    :
    ∃ final, BatchedWeightsCallerSafeCadenceV4.queryStep
      (BatchedWeightsCallerRangeTraversalV1.rangeVisits n BatchedWeightsCallerNaturalIndexV1.rangeIndexAt powerAt basisAt) state = Result.ok final ∧
      GlobalRawPhaseBound final ∧ final.raw.val.length = state.raw.val.length ∧
      final.terms.val = state.terms.val + 1 := by
  have hterms : state.terms = 0#usize := by
    exact (BatchedWeightsNewSuccessContentsBoundsV2.new_success_contents_bounds weights state hnew).1
  have htermsVal : state.terms.val = 0 := by
    have ht := congrArg UScalar.val hterms
    simpa using ht
  have hglobal : GlobalRawPhaseBound state :=
    BatchedWeightsNewInitialGlobalBoundV2.new_success_global_raw_phase_bound weights state hnew
  obtain ⟨_, hrawlen, _⟩ :=
    BatchedWeightsNewSuccessContentsBoundsV2.new_success_contents_bounds weights state hnew
  have hlen : n = state.raw.val.length := calc
    n = (Slice.len weights).val := hnlen
    _ = state.raw.val.length := hrawlen.symm
  have hbits : 256 < 2 ^ UScalarTy.Usize.numBits := by
    rw [UScalarTy.Usize_numBits_eq, ← Std.Usize.max_succ_eq_pow]
    have hm := Std.Usize.cMax_bound_concrete.1
    omega
  have hn : n < 2 ^ UScalarTy.Usize.numBits := by omega
  have hroom : state.terms.val + 1 ≤ Std.Usize.max := by
    rw [htermsVal]
    have hm := Std.Usize.cMax_bound_concrete.1
    omega
  have hsum : state.terms.val + (1#usize).val ≤ Std.Usize.max := by
    simpa using hroom
  have hspec : UScalar.add state.terms (1#usize)
      ⦃ z => z.val = state.terms.val + 1 ⦄ := by
    apply UScalar.add_spec
    simpa only [UScalar.max_USize_eq] using hsum
  obtain ⟨nextTerms, hinc, _⟩ := WP.spec_imp_exists hspec
  exact natural_range_query_global n state hn hlen hglobal powerAt basisAt
    hpower0a hpower0b hpower1a hpower1b hbasis ⟨nextTerms, hinc⟩
#print axioms successful_new_then_natural_query_global
end BatchedWeightsNewQueryCallerV1
