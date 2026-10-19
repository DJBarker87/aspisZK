import BatchedWeightsSelectedPushGeneralFrameV1
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace BatchedWeightsCallerSafeCadenceV2
open AspisR1BatchedWeightsExtraction
open BatchedWeightsSelectedPushGeneralFrameV1

abbrev BW := BatchedWeightsSelectedPushGeneralFrameV1.BW
abbrev Usize := UScalar UScalarTy.Usize
abbrev Q := BatchedWeightsSelectedPushGeneralFrameV1.Q
abbrev M := BatchedWeightsSelectedPushGeneralFrameV1.M

structure RowVisit where
  index : Usize
  power : Q
  basis : M

def pushRows : List RowVisit → BW → Result BW
  | [], state => .ok state
  | visit :: rest, state => do
      let state' ← batched_weights.BatchedWeights.push
        state visit.index visit.power visit.basis
      pushRows rest state'

def incrementTerms (state : BW) : Result BW := do
  let terms ← state.terms + 1#usize
  ok { state with terms }

def queryStep (visits : List RowVisit) (state : BW) : Result BW := do
  let afterRows ← pushRows visits state
  incrementTerms afterRows

def runQueries : List (List RowVisit) → BW → Result BW
  | [], state => .ok state
  | visits :: rest, state => do
      let state' ← queryStep visits state
      runQueries rest state'

def counterCadence : List (List RowVisit) → Usize → Result Usize
  | [], terms => .ok terms
  | _ :: rest, terms => do
      let terms' ← terms + 1#usize
      counterCadence rest terms'

/-- The exact sufficient arithmetic preconditions consumed by the proved
selected-push theorem for one source row visit. -/
structure PushAdmissible (visit : RowVisit) (state : BW) : Prop where
  indexValid : visit.index.val < state.raw.length
  rawBound : ∀ k : Usize, ∀ hk : k.val < 4,
    AspisR1BatchedWeightsPushLoopGlobalFrameV1.cellAt state visit.index indexValid k hk <
      2^34 + state.terms.val % 4 * AspisR1BatchedAllPrefix.cap
  power0a : visit.power.c0.a.val < AspisV8R17.RawReducer.P
  power0b : visit.power.c0.b.val < AspisV8R17.RawReducer.P
  power1a : visit.power.c1.a.val < AspisV8R17.RawReducer.P
  power1b : visit.power.c1.b.val < AspisV8R17.RawReducer.P
  basis : visit.basis.val < AspisV8R17.RawReducer.P

inductive SafeRows : List RowVisit → BW → BW → Prop where
  | nil (state : BW) : SafeRows [] state state
  | cons (visit : RowVisit) (rest : List RowVisit) (state final : BW)
      (hsafe : PushAdmissible visit state)
      (htail : ∀ mid : BW,
        batched_weights.BatchedWeights.push state visit.index visit.power visit.basis = .ok mid →
        SafeRows rest mid final) : SafeRows (visit :: rest) state final

theorem safeRows_actual (rows : List RowVisit) (initial final : BW)
    (h : SafeRows rows initial final) : pushRows rows initial = .ok final := by
  induction rows generalizing initial final with
  | nil =>
      cases h
      rfl
  | cons visit rest ih =>
      cases h with
      | cons visit' rest' state final hsafe htail =>
          obtain ⟨mid,hpush,hterms,hlen,hframe⟩ :=
            selected_push_preserves_outer_frame visit.index initial visit.power visit.basis
              hsafe.indexValid hsafe.rawBound hsafe.power0a hsafe.power0b
              hsafe.power1a hsafe.power1b hsafe.basis
          have htail' := htail mid hpush
          simp [pushRows, hpush, ih mid final htail']

theorem safeRows_terms (rows : List RowVisit) (initial final : BW)
    (h : SafeRows rows initial final) : final.terms = initial.terms := by
  induction rows generalizing initial final with
  | nil =>
      cases h
      rfl
  | cons visit rest ih =>
      cases h with
      | cons visit' rest' state final hsafe htail =>
          obtain ⟨mid,hpush,hterms,hlen,hframe⟩ :=
            selected_push_preserves_outer_frame visit.index initial visit.power visit.basis
              hsafe.indexValid hsafe.rawBound hsafe.power0a hsafe.power0b
              hsafe.power1a hsafe.power1b hsafe.basis
          have htail' := htail mid hpush
          exact (ih mid final htail').trans hterms

inductive SafeQueries : List (List RowVisit) → BW → BW → Prop where
  | nil (state : BW) : SafeQueries [] state state
  | cons (rows : List RowVisit) (rest : List (List RowVisit))
      (state mid final : BW) (nextTerms : Usize)
      (hrows : SafeRows rows state mid)
      (hinc : (mid.terms + 1#usize : Result Usize) = Result.ok nextTerms)
      (htail : SafeQueries rest { mid with terms := nextTerms } final) :
      SafeQueries (rows :: rest) state final

theorem safeQueries_actual (queries : List (List RowVisit)) (initial final : BW)
    (h : SafeQueries queries initial final) : runQueries queries initial = .ok final := by
  induction h with
  | nil state => rfl
  | @cons rows rest state mid final nextTerms hrows hinc htail ih =>
      have hstep : queryStep rows state = .ok { mid with terms := nextTerms } := by
        simp [queryStep, incrementTerms, safeRows_actual rows state mid hrows, hinc]
      simp [runQueries, hstep, ih]

theorem safeQueries_counterCadence (queries : List (List RowVisit))
    (initial final : BW) (h : SafeQueries queries initial final) :
    counterCadence queries initial.terms = .ok final.terms := by
  induction h with
  | nil state => rfl
  | @cons rows rest state mid final nextTerms hrows hinc htail ih =>
      have hterms := safeRows_terms rows state mid hrows
      have hinc' : (state.terms + 1#usize : Result Usize) = Result.ok nextTerms := by
        rw [← hterms]
        exact hinc
      simp [counterCadence, hinc', ih]

#print axioms safeRows_actual
#print axioms safeRows_terms
#print axioms safeQueries_actual
#print axioms safeQueries_counterCadence
end BatchedWeightsCallerSafeCadenceV2
