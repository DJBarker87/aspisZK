import AspisOneTxMergedBudget
import AspisOneTxMergedRecovery
import AspisAcceptanceLink
import AspisRows40Protocol
import R1SelectedFieldSequenceCodec
import OraclePortFrozenOrderDecision
import AspisLib_Guard

/-! The Aspis one-transaction verifier: the model terminal decision `dV_aspis`
(item M5) and its typed batched check `verifyS` (item M4) of
ONE-TRANSACTION-GAME.md.

Kind of result: MODEL DEFINITIONS AND THEOREMS in R1's stored-decision model.
`dV_aspis` is a copy of R1's `OraclePortFrozenOrder.dV_frozen` (not of the
two-transaction `dV_frozen2`; there is no checkpoint) with:
* the six 10/12-position slots replaced by the three merged slots
  (`verifyMergedAll`, AspisOneTxMergedSlot);
* R1's 33-round guard, parser alignment, query read and source-input read
  applied to the first 33 rounds (`take33 tr`), plus: 40 rounds, and rounds
  34..39 carry the stored certificate frames;
* R1's typed check `D0TypedChecks.verify` replaced by `verifyS`: R1's per-query
  first-fold check (`R16DecisionQueryModel.verify`), R1's batched second-fold
  closed sum and the first pairing conjunct are removed; the batched
  first-fold equation (`FirstBatch`) and the final sumcheck's reads and final
  check (`FinalPart`) are added; the two boundary conjuncts and R1's semantic
  equations stay.
`decodePairS` fixes the acceptance link's codec parameter: the 64-byte payload
of a 64-byte frame, decoded as two canonical wide-field values with R1's
codec (`SelectedFieldSequenceCodec.decodeWide`, which accepts exactly the
encodings it produces, `encodeWide_of_decode`).

NOT established here: that the Rust (`verify_summed_format`, fused.rs:812)
computes `dV_aspis` (source refinement); in particular that `E::from_le_bytes`
is `FoldedLeafCodec.decodeWide` (the same correspondence R1 needs for its
folded leaf values). -/
set_option autoImplicit false
noncomputable section
namespace AspisOneTx
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisR1 AspisR1.OraclePortCompactDraft AspisR1.OraclePortSelectedDraft
open AspisR1.OraclePortStoredDecisionDraftC4
open AspisFuture.StageD
open AspisAcceptance (EW KQ Rounds Codec FirstBatch FinalCheck)
open RawCutTranscriptRun (ErasedPrefix ErasedMessage)
open RecordedBinaryExperimentBin (SourceInputs)
attribute [local instance] Classical.propDecidable

/-! ### The codec of rows 33 to 39 -/

/-- The two canonical wide-field values of a row-33..39 message: the 64-byte
payload of a 64-byte frame (`AspisRows40.Protocol.payloadOf`), decoded with
R1's canonical wide codec. -/
def decodePairS (m : LiteralTranscript.Message) : Option (EW × EW) :=
  (AspisRows40.Protocol.payloadOf (LiteralTranscript.erase m)).bind fun pl =>
    (SelectedFieldSequenceCodec.decodeWide 2 pl).map fun xs => (xs 0, xs 1)

/-- Enrichment of the words (rows 0, 2, 30) does not change the codec's read. -/
theorem decodePairS_enrich (w : CanonicalCutEnrichedTranscript.Words) (m : LiteralTranscript.Message) :
    decodePairS (CanonicalCutEnrichedTranscript.enrichMessage w m) = decodePairS m := by
  cases m <;> rfl

/-- Canonicality: a successful read determines the payload bytes. -/
theorem decodePairS_canonical (m : LiteralTranscript.Message) (x y : EW)
    (h : decodePairS m = some (x, y)) : ∃ pl xs,
      AspisRows40.Protocol.payloadOf (LiteralTranscript.erase m) = some pl ∧
      SelectedFieldSequenceCodec.decodeWide 2 pl = some xs ∧ xs 0 = x ∧ xs 1 = y ∧
      SelectedFieldSequenceCodec.encodeWide xs = pl := by
  unfold decodePairS at h
  cases hp : AspisRows40.Protocol.payloadOf (LiteralTranscript.erase m) with
  | none => simp [hp] at h
  | some pl =>
    simp only [hp, Option.bind_some] at h
    cases hd : SelectedFieldSequenceCodec.decodeWide 2 pl with
    | none => simp [hd] at h
    | some xs =>
      simp only [hd, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨pl, xs, rfl, hd, h.1, h.2,
        SelectedFieldSequenceCodec.encodeWide_of_decode pl xs hd⟩

/-! ### The typed batched check (M4) -/

/-- R1's two boundary conjuncts of `MatchingSupport.AcceptedPairing`
(the acceptance link's `roundBoundaries`). -/
def Boundaries (data : MatchingSupport.Data EW) : Prop :=
  AspisR1.TwoRoundComparison.boundary data.p1 =
      AspisR1.RoundPairing.quarter * data.p0.eval data.alpha0 ∧
    AspisR1.TwoRoundComparison.boundary data.p0 =
      AspisR1.RoundPairing.quarter *
        AspisR1.JointFunctionalBinding.claimedValue data.Y data.c0 data.gamma data.kappa

/-- The final sumcheck's reads and final check on the 40 rounds, exactly the
corresponding fields of `AspisAcceptance.AspisChecks` at `decodePairS`. -/
def FinalPart (rs : Rounds) (data : MatchingSupport.Data EW) (q : Fin 22 → Fin 262144)
    (rho : KQ) : Prop :=
  ∃ (m33 : LiteralTranscript.Message) (lamV : EW) (state33 : State) (claimS rhs2 : EW)
    (rounds : List (KQ × EW × EW)) (roundsLen : rounds.length = 6),
    rs[33]? = some (m33, (TranscriptView.Value.ordinary lamV, state33)) ∧
    decodePairS m33 = some (claimS, rhs2) ∧
    claimS = data.p1.eval data.alpha1 ∧
    rhs2 = rhs2Of LiteralOpeningView.eK rho (QueryResidualBridge.values data q) ∧
    (∀ b (hb : b < 6), ∃ mb vb sb,
      rs[34 + b]? = some (mb, (TranscriptView.Value.ordinary vb, sb)) ∧
      decodePairS mb = some ((rounds[b]'(by rw [roundsLen]; exact hb)).2.1,
        (rounds[b]'(by rw [roundsLen]; exact hb)).2.2) ∧
      (rounds[b]'(by rw [roundsLen]; exact hb)).1 = SelectedChallengeMap.rhoOf vb) ∧
    FinalCheck LiteralOpeningView.eK rounds claimS rhs2 (SelectedChallengeMap.rhoOf lamV) rho data q

/-- The Aspis typed check: R1's `D0TypedChecks.verify` with the per-query
first-fold check, the closed second-fold sum and the first pairing conjunct
replaced by the batched first-fold equation and the final sumcheck. -/
def verifyS (rs : Rounds) (i : SourceInputs) : Bool :=
  match LiteralMatchingData.read (rs.take 33) with
  | none => false
  | some data => decide (
      data = i.data ∧
      Boundaries data ∧
      R3SemanticRemainingJoins.EquationEndpoint i.decoded (rs.take 33) data ∧
      ∀ q : Fin 22 → Fin 262144, LiteralQueryRead.decode i.queryBytes = some q →
        FirstBatch LiteralOpeningView.eK (SelectedChallengeMap.rhoOf i.rho) data q ∧
        FinalPart rs data q (SelectedChallengeMap.rhoOf i.rho))

theorem verifyS_accepted (rs : Rounds) (i : SourceInputs) (h : verifyS rs i = true) :
    LiteralMatchingData.read (rs.take 33) = some i.data ∧
    Boundaries i.data ∧
    R3SemanticRemainingJoins.EquationEndpoint i.decoded (rs.take 33) i.data ∧
    ∀ q : Fin 22 → Fin 262144, LiteralQueryRead.decode i.queryBytes = some q →
      FirstBatch LiteralOpeningView.eK (SelectedChallengeMap.rhoOf i.rho) i.data q ∧
      FinalPart rs i.data q (SelectedChallengeMap.rhoOf i.rho) := by
  unfold verifyS at h
  cases hr : LiteralMatchingData.read (rs.take 33) with
  | none => simp [hr] at h
  | some data =>
    simp only [hr, decide_eq_true_eq] at h
    obtain ⟨same, rest⟩ := h
    subst same
    exact ⟨rfl, rest⟩

/-! ### The decision (M5) -/

/-- The first 33 rounds, where R1's guard, parser alignment and reads apply. -/
def take33 (tr : ErasedPrefix) : ErasedPrefix := ⟨tr.statement, tr.rounds.take 33⟩

/-- Rounds 34..39 carry the stored certificate frames (the Rust absorbs the
certificate's 64-byte rows, fused.rs:526-530). -/
def AlignedCert (p : Parsed) (tr : ErasedPrefix) : Prop :=
  ∀ b, b < 6 → ∃ msg c, tr.rounds[34 + b]? = some (.payload msg, c) ∧
    msg.val = framed (slice p.wire (certificateStart + 64*b) 64)

def parseReachedS (stored : Bytes) (tr : ErasedPrefix) : Option Parsed := do
  let p ← parseSummed stored
  if Aligned p (take33 tr) ∧ AlignedCert p tr then some p else none

theorem parsedS (stored : Bytes) (tr : ErasedPrefix) (p : Parsed)
    (h : parseReachedS stored tr = some p) :
    parseSummed stored = some p ∧ p.wire = stored ∧ Aligned p (take33 tr) ∧ AlignedCert p tr := by
  unfold parseReachedS at h
  cases hp : parseSummed stored with
  | none => simp [hp] at h
  | some p' =>
    by_cases ha : Aligned p' (take33 tr) ∧ AlignedCert p' tr
    · simp [hp, ha] at h
      subst p
      exact ⟨rfl, (parseSummed_header _ _ hp).2, ha⟩
    · simp [hp, ha] at h

def arithmeticS (p : Parsed) (q : Fin 22 → Fin 262144) (tr : ErasedPrefix) : Bool :=
  match input p q (take33 tr) with
  | none => false
  | some i => verifyS (typedRows p q tr) i

/-- The Aspis terminal decision (copy of `OraclePortFrozenOrder.dV_frozen`). -/
def dV_aspis : OraclePortStoredExperimentC4.Decision := fun stored tr _ =>
  if OraclePortAdmission.Guard (take33 tr) ∧ tr.rounds.length = 40 then
    match parseReachedS stored tr, queries (take33 tr) with
    | some p, some q =>
        bind (verifyMergedAll p q) fun ok => .done (ok && arithmeticS p q tr)
    | _, _ => .done false
  else .done false

/-- Copy of `OraclePortFrozenOrder.accepted` / `accepted_details`. -/
theorem accepted_detailsS (stored : Bytes) (tr : ErasedPrefix) (m : ErasedMessage)
    (H : Bytes → State) (ha : (eval H (dV_aspis stored tr m)).2 = true) :
    OraclePortAdmission.Guard (take33 tr) ∧ tr.rounds.length = 40 ∧ ∃ p q i,
      parseReachedS stored tr = some p ∧ queries (take33 tr) = some q ∧
      (eval H (verifyMergedAll p q)).2 = true ∧
      input p q (take33 tr) = some i ∧ verifyS (typedRows p q tr) i = true := by
  unfold dV_aspis at ha
  split at ha
  · rename_i guard
    split at ha
    · rename_i p q hp hq
      simp only [eval_bind, eval, Bool.and_eq_true] at ha
      obtain ⟨merkle, arith⟩ := ha
      unfold arithmeticS at arith
      cases hi : input p q (take33 tr) with
      | none => simp [hi] at arith
      | some i =>
        simp only [hi] at arith
        exact ⟨guard.1, guard.2, p, q, i, hp, hq, merkle, hi, arith⟩
    · simp [eval] at ha
  · simp [eval] at ha

/-- All-input issued-call budget of the decision: the merged multiproofs only. -/
theorem decision_budgetS (stored : Bytes) (H : Bytes → State) (tr : ErasedPrefix) (m : ErasedMessage) :
    (eval H (dV_aspis stored tr m)).1.length ≤ 975 := by
  unfold dV_aspis
  split
  · split
    · rename_i p q _ _
      have b := mergedAll_budget H p q
      simp only [eval_bind, eval, List.append_nil]
      exact b
    · simp [eval]
  · simp [eval]

/-- R1's decision budget (1,046, `OraclePortStoredExperimentC4.Budget`) holds. -/
theorem decision_budget_r1 : OraclePortStoredExperimentC4.Budget dV_aspis := by
  intro stored H tr m
  exact (decision_budgetS stored H tr m).trans (by decide)

#print axioms decodePairS_enrich
#print axioms decodePairS_canonical
#print axioms verifyS_accepted
#print axioms parsedS
#print axioms accepted_detailsS
#print axioms decision_budgetS
#print axioms decision_budget_r1
end AspisOneTx
end
