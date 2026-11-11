import AspisAcceptanceLink
import LiteralDecoderEnrichment
import AspisRowDensityCaps

/-! Plan item 8: the Aspis 40-row classifier with its budgets.

`AspisAcceptance.bad decodePair` is R1's classifier below round 32, the
residual-pair event at round 32, the combining-challenge event at 33 and the
round events at 34 to 39. Its budgets (`budget40`): R1's budget below 32,
`capPair` (= R1's `rhoCap`) at 32, `capLambda` at 33, `capRound` at 34 to 39.

* `literal_density`, `erased_density`: rows 0 to 32, the classifier's
  independent-answer density on R1's literal prefix, and its copy on the
  erased prefix with restored words (copy of R1's
  `LiteralDecoderEnrichment.density`).
* Rows 33 to 39 in the shape of the row-densities agent's
  `Sampler.{combining,round}_unified_density`: the reads `read33`, `readR`
  of `(P, m)`, the bad sets `S33`, `SR n` of sizes at most 1 and 2, and the
  identities `finalEvent_iff33`, `finalEvent_iffR` between the classifier's
  event and `x ∈ S (read (P, m))`.

Kind of result: model theorems about R1's literal transcript carrier and the
classifier; no source statement. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace AspisClassifier40
open scoped BigOperators
open FS FS2 Finset
open AspisR1 AspisAcceptance
open AspisFuture.StageD
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.OracleResampling
open AspisV8R19.CausalFirstHitUnionBound
open AspisRowDensity.QM31

/-- The budget of each row of the 40-row classifier. -/
def budget40 (n : ℕ) : ℚ :=
  if n < 32 then LiteralClassifier.budget n
  else if n = 32 then capPair
  else if n = 33 then capLambda
  else if n < 40 then capRound
  else 0

theorem budget40_lt32 (n : ℕ) (h : n < 32) : budget40 n = LiteralClassifier.budget n := by
  unfold budget40; rw [if_pos h]

theorem budget40_32 : budget40 32 = LiteralClassifier.budget 32 := by
  unfold budget40
  rw [if_neg (by omega), if_pos rfl, AspisRowDensity.Caps.budget32_eq_capPair]

/-- Rows 0 to 32: the classifier's density on R1's literal prefix. -/
theorem literal_density (decodePair : Codec) (P : LiteralTranscript.Prefix)
    (m : LiteralTranscript.Message) (hi : P.round < 33) :
    independentMean (LiteralTranscript.samp P.round P m).toProgram
      (fun v => indicator (bad decodePair P m v.2)) ≤ budget40 P.round := by
  by_cases h32 : P.round < 32
  · have h := LiteralClassifier.density P m hi
    have heq : ∀ c, indicator (bad decodePair P m c) = indicator (LiteralClassifier.bad P m c) :=
      fun c => indicator_iff (bad_lt32 P m c h32)
    simp only [heq]
    rw [budget40_lt32 _ h32]
    exact h
  · have hr : P.round = 32 := by omega
    have h := AspisPairResidual.Row32.row32_pair_density P m hr
    have heq : ∀ c, indicator (bad decodePair P m c) =
        indicator (LiteralOrdinaryDensity.event P m (AspisPairResidual.Row32.bad P) c) :=
      fun c => indicator_iff (bad_eq32 P m c hr)
    simp only [heq]
    rw [hr, budget40_32, AspisRowDensity.Caps.budget32_eq_capPair, capPair_eq_rhoCap]
    rw [hr] at h
    exact h

open LiteralDecoderEnrichment CanonicalCutEnrichedTranscript in
/-- Rows 0 to 32 on the erased prefix with restored words (copy of R1's
`LiteralDecoderEnrichment.density` for the Aspis classifier). -/
theorem erased_density (decodePair : Codec) (w : Words) (P : ErasedPrefix) (m : ErasedMessage)
    (hi : P.round < 33) :
    independentMean (UnifiedSampler.samp SelectedTranscriptParams.params
      (by norm_num [SelectedTranscriptParams.params, SelectedTranscriptParams.D])
      P.round P m).toProgram
      (fun v => indicator (bad decodePair (restorePrefix w P) (message w P.round m) v.2)) ≤
      budget40 P.round := by
  have h := literal_density decodePair (restorePrefix w P) (message w P.round m) (by simpa using hi)
  simpa only [prefix_round, LiteralTranscript.samp, erase_prefix, erase_message] using h

/-! ## Rows 33 to 39 in the row-densities shape -/

abbrev X33 := MatchingSupport.Data EW × (Fin 22 → Fin 262144) × KQ × EW × EW

/-- Read of row 33's bad set from `(P, m)`. -/
def read33 (decodePair : Codec) (P : LiteralTranscript.Prefix) (m : LiteralTranscript.Message) :
    Option X33 :=
  match LiteralRhoDensity.read ⟨P.statement, P.rounds.take 32⟩, valueAt P.rounds 32, decodePair m with
  | some (d, q), some vr, some (a, b) => some (d, q, SelectedChallengeMap.rhoOf vr, a, b)
  | _, _, _ => none

def S33 (x : X33) : Finset KQ :=
  lamBadSet LiteralOpeningView.eK x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2

theorem S33_card (x : X33) : (S33 x).card ≤ 1 := by
  unfold S33 lamBadSet
  exact lambdaBad_card_le_one _ _ _

abbrev XR := MatchingSupport.Data EW × (Fin 22 → Fin 262144) × KQ × KQ × EW × EW ×
  List (KQ × EW × EW) × EW × EW

/-- Read of the bad set of rows 34 to 39 from `(P, m)`. -/
def readR (decodePair : Codec) (P : LiteralTranscript.Prefix) (m : LiteralTranscript.Message) :
    Option XR :=
  match LiteralRhoDensity.read ⟨P.statement, P.rounds.take 32⟩, valueAt P.rounds 32, decodePair m with
  | some (d, q), some vr, some (a, b) =>
    match valueAt P.rounds 33, (P.rounds[33]?).bind (fun mc => decodePair mc.1),
        roundsAt decodePair P.rounds (P.round - 34) with
    | some vl, some (cS, r2), some pre =>
        some (d, q, SelectedChallengeMap.rhoOf vr, SelectedChallengeMap.rhoOf vl, cS, r2, pre, a, b)
    | _, _, _ => none
  | _, _, _ => none

def SR (n : ℕ) (x : XR) : Finset KQ :=
  roundBadSet LiteralOpeningView.eK x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2.1
    (n - 34) x.2.2.2.2.2.2.1 x.2.2.2.2.2.2.2.1 x.2.2.2.2.2.2.2.2

theorem SR_card (n : ℕ) (x : XR) : (SR n x).card ≤ 2 := by
  unfold SR roundBadSet
  exact roundBad_card_le_two _ _ (roundPoly_natDegree_le _ _ _) _ _ _

/-- At round 33 the classifier's event is membership in `S33 (read33 (P, m))`. -/
theorem finalEvent_iff33 (decodePair : Codec) (P : LiteralTranscript.Prefix)
    (m : LiteralTranscript.Message) (x : KQ) (h : P.round = 33) :
    finalEvent decodePair P m x ↔
      (match read33 decodePair P m with | none => False | some y => x ∈ S33 y) := by
  unfold finalEvent read33
  cases h1 : LiteralRhoDensity.read ⟨P.statement, P.rounds.take 32⟩ with
  | none => simp only []
  | some dq =>
    obtain ⟨d, q⟩ := dq
    cases h2 : valueAt P.rounds 32 with
    | none => simp only []
    | some vr =>
      cases h3 : decodePair m with
      | none => simp only []
      | some ab =>
        obtain ⟨a, b⟩ := ab
        simp only [h, if_true, S33]

/-- At rounds 34 to 39 the classifier's event is membership in `SR n (readR (P, m))`. -/
theorem finalEvent_iffR (decodePair : Codec) (P : LiteralTranscript.Prefix)
    (m : LiteralTranscript.Message) (x : KQ) (n : ℕ) (h : P.round = n) (hlo : 34 ≤ n)
    (hhi : n < 40) :
    finalEvent decodePair P m x ↔
      (match readR decodePair P m with | none => False | some y => x ∈ SR n y) := by
  have h33 : ¬ (P.round = 33) := by omega
  have h40 : P.round < 40 := by omega
  unfold finalEvent readR
  cases h1 : LiteralRhoDensity.read ⟨P.statement, P.rounds.take 32⟩ with
  | none => simp only []
  | some dq =>
    obtain ⟨d, q⟩ := dq
    cases h2 : valueAt P.rounds 32 with
    | none => simp only []
    | some vr =>
      cases h3 : decodePair m with
      | none => simp only []
      | some ab =>
        obtain ⟨a, b⟩ := ab
        simp only [h33, h40, if_false, if_true]
        cases h4 : valueAt P.rounds 33 with
        | none => simp only []
        | some vl =>
          cases h5 : (P.rounds[33]?).bind (fun mc => decodePair mc.1) with
          | none => simp only []
          | some cr =>
            obtain ⟨cS, r2⟩ := cr
            cases h6 : roundsAt decodePair P.rounds (P.round - 34) with
            | none => simp only []
            | some pre =>
              simp only [SR, h]

#print axioms literal_density
#print axioms erased_density
#print axioms S33_card
#print axioms SR_card
#print axioms finalEvent_iff33
#print axioms finalEvent_iffR
end AspisClassifier40
end
