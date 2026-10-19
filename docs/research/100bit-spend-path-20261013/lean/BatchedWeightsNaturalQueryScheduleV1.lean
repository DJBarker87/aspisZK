import BatchedWeightsNaturalRangeQueryGlobalV1
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace BatchedWeightsNaturalQueryScheduleV1
open BatchedWeightsNaturalRangeQueryGlobalV1
open BatchedWeightsCallerNaturalIndexV1
open BatchedWeightsCallerGlobalRangeBridgeV1
open BatchedWeightsCallerRangeTraversalV1
open BatchedWeightsCallerSafeCadenceV4

abbrev BW := BatchedWeightsNaturalRangeQueryGlobalV1.BW
abbrev Usize := UScalar UScalarTy.Usize
abbrev Q := BatchedWeightsNaturalRangeQueryGlobalV1.Q
abbrev M := BatchedWeightsNaturalRangeQueryGlobalV1.M

structure QueryInput where
  powerAt : Nat → Q
  basisAt : Nat → M

def inputRows (n : Nat) (q : QueryInput) : List RowVisit :=
  rangeVisits n rangeIndexAt q.powerAt q.basisAt

def runNaturalQueries (n : Nat) : List QueryInput → BW → Result BW
  | [], state => .ok state
  | q :: rest, state => do
      let state' ← queryStep (inputRows n q) state
      runNaturalQueries n rest state'

def CanonicalInput (n : Nat) (q : QueryInput) : Prop :=
  (∀ i, i < n → (q.powerAt i).c0.a.val < AspisV8R17.RawReducer.P) ∧
  (∀ i, i < n → (q.powerAt i).c0.b.val < AspisV8R17.RawReducer.P) ∧
  (∀ i, i < n → (q.powerAt i).c1.a.val < AspisV8R17.RawReducer.P) ∧
  (∀ i, i < n → (q.powerAt i).c1.b.val < AspisV8R17.RawReducer.P) ∧
  (∀ i, i < n → (q.basisAt i).val < AspisV8R17.RawReducer.P)

private theorem usize_add_one (a : Usize) (hsum : a.val + 1 ≤ Usize.max) :
    ∃ b : Usize, UScalar.add a 1#usize = .ok b ∧ b.val = a.val + 1 := by
  have hsum' : a.val + (1#usize).val ≤ Usize.max := by simpa using hsum
  have hchecked : UScalar.add a 1#usize ⦃ z => z.val = a.val + 1 ⦄ := by
    apply UScalar.add_spec
    simpa only [UScalar.max_USize_eq] using hsum'
  exact WP.spec_imp_exists hchecked

/-- The actual repeated ascending-range query caller preserves the global
phase envelope. Each round executes the concrete checked `queryStep` (all
row pushes followed by exactly one checked terms increment); canonical row
operands and an initial counter-room bound are the caller obligations. -/
theorem runNaturalQueries_global
    (n : Nat) (queries : List QueryInput) (state : BW)
    (hn : n < 2^UScalarTy.Usize.numBits)
    (hlen : n = state.raw.val.length)
    (hglobal : GlobalRawPhaseBound state)
    (hcanonical : ∀ q, q ∈ queries → CanonicalInput n q)
    (hroom : state.terms.val + queries.length ≤ Usize.max) :
    ∃ final, runNaturalQueries n queries state = .ok final ∧
      GlobalRawPhaseBound final ∧
      final.raw.val.length = state.raw.val.length ∧
      final.terms.val = state.terms.val + queries.length := by
  induction queries generalizing state with
  | nil =>
      refine ⟨state, rfl, hglobal, rfl, ?_⟩
      simp
  | cons q rest ih =>
      have hq := hcanonical q (by simp)
      rcases hq with ⟨hp0a,hp0b,hp1a,hp1b,hb⟩
      have hsum : state.terms.val + 1 ≤ Usize.max := by
        have hlenRest : rest.length + 1 = (q :: rest).length := by simp
        omega
      obtain ⟨nextTerms,hinc,hnextVal⟩ := usize_add_one state.terms hsum
      obtain ⟨mid,hstep,hmidGlobal,hmidLen,hmidTerms⟩ :=
        natural_range_query_global n state hn hlen hglobal
          q.powerAt q.basisAt hp0a hp0b hp1a hp1b hb ⟨nextTerms,hinc⟩
      have hroomTail : mid.terms.val + rest.length ≤ Usize.max := by
        have hlenRest : rest.length + 1 = (q :: rest).length := by simp
        rw [hmidTerms]
        omega
      have hcanTail : ∀ q', q' ∈ rest → CanonicalInput n q' := by
        intro q' hq'
        exact hcanonical q' (by simp [hq'])
      have hlenMid : n = mid.raw.val.length := by rw [hmidLen]; exact hlen
      obtain ⟨final,hrun,hfinalGlobal,hfinalLen,hfinalTerms⟩ :=
        ih mid hlenMid hmidGlobal hcanTail hroomTail
      refine ⟨final, ?_, hfinalGlobal, ?_, ?_⟩
      · simp [runNaturalQueries, inputRows, hstep, hrun]
      · omega
      · rw [hfinalTerms]
        rw [hmidTerms]
        have hlenRest : rest.length + 1 = (q :: rest).length := by simp
        omega

#print axioms runNaturalQueries_global
end BatchedWeightsNaturalQueryScheduleV1
