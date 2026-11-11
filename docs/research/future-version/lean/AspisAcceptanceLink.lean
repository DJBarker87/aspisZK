import AspisAcceptanceAlgebra
import AspisPairResidualDensity
import R1LiteralAcceptanceTerminal
import R1LiteralRhoBinding
import R1LiteralReadStability
import R1GenericNoHitIndex

/-! The Aspis one-transaction verifier, acceptance-to-extraction link, part 2
(item 11 of ASPIS-INSTANCE-PLAN.md): on a 40-round literal transcript, the
Aspis checks and no hit of the Aspis classifier give R1's `Checks` and R1's
no-hit on the first 33 rounds, so R1's `checks_noHit_relation` applies.

Kind of result: MODEL THEOREM about R1's literal transcript carrier (which
holds rows 33 to 39 as `.payload` messages; `AspisRows40.Literal`). The
checks are model conditions on the transcript, as R1's `Checks` is; "an
accepted Aspis verifier run supplies `AspisChecks`" is the
commitment-recovery layer (plan item 15), NOT proved here.

Parameter (not a hypothesis about security): `decodePair`, the codec reading
the two 32-byte field values of a 64-byte payload message of rows 33 to 39
(`claim ‖ rhs2` at row 33, `c0 ‖ c2` at rows 34 to 39). Every read below that
uses it is fixed by the row's own message and the earlier rounds, before the
row's challenge.

Classifier (`bad`): R1's below round 32; at round 32 the residual-pair event
`AspisPairResidual.Row32.bad` (pair-binding agent) in R1's ordinary-row shape;
at rounds 33 to 39 `finalBad`, reading `(P, m)`: the combining-challenge
event `lambdaBad` at 33 and the round events `roundBad` at 34 to 39, with the
round's bad set read from the earlier rounds. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace AspisAcceptance
open scoped BigOperators
open FS FS2 Finset
open AspisR1
open AspisFuture.StageD
open R0P R0P.Mask R0P.SemSource R0P.SemRounds R0C.SemStatement
open AspisR1.LiteralTranscript
open AspisV8R15.ExactTowerBase
open AspisWideTower AspisCircleGroupOrder SpendRelation
open AspisV8R19.SourceDuplexStep

abbrev EW := AspisWideTower.WideExact
abbrev KQ := AspisV8R15.ExactTowerBase.QM31Exact
abbrev Rounds := List (LiteralTranscript.Message × LiteralTranscript.Challenge)
abbrev Codec := LiteralTranscript.Message → Option (EW × EW)

/-- The ordinary challenge value of round `i`, if any. -/
def valueAt (rs : Rounds) (i : ℕ) : Option EW :=
  rs[i]?.bind fun mc =>
    match mc.2.1 with
    | TranscriptView.Value.ordinary v => some v
    | _ => none

/-- The first `b` rounds of the final sumcheck (rows 34 .. 33+b), read from
the transcript: the challenge and the two certificate values of each. -/
def roundsAt (decodePair : Codec) (rs : Rounds) : ℕ → Option (List (KQ × EW × EW))
  | 0 => some []
  | b + 1 => (roundsAt decodePair rs b).bind fun pre =>
      (valueAt rs (34 + b)).bind fun v =>
        (rs[34 + b]?.bind fun mc => decodePair mc.1).map fun x =>
          pre ++ [(SelectedChallengeMap.rhoOf v, x.1, x.2)]

/-- The event of rows 33 to 39 at challenge `x`, read from `(P, m)`: the
data, queries and ρ from the first 32 rounds (`LiteralRhoDensity.read`, R1's
reader), the row's message through `decodePair`, and for rows 34 to 39 also
λ, the row-33 message and the earlier rounds. -/
def finalEvent (decodePair : Codec) (P : LiteralTranscript.Prefix)
    (m : LiteralTranscript.Message) (x : KQ) : Prop :=
  match LiteralRhoDensity.read ⟨P.statement, P.rounds.take 32⟩, valueAt P.rounds 32, decodePair m with
  | some (d, q), some vr, some (a, b) =>
    if P.round = 33 then
      x ∈ lamBadSet LiteralOpeningView.eK d q (SelectedChallengeMap.rhoOf vr) a b
    else if P.round < 40 then
      match valueAt P.rounds 33, (P.rounds[33]?).bind (fun mc => decodePair mc.1),
          roundsAt decodePair P.rounds (P.round - 34) with
      | some vl, some (cS, r2), some pre =>
          x ∈ roundBadSet LiteralOpeningView.eK d q (SelectedChallengeMap.rhoOf vr)
            (SelectedChallengeMap.rhoOf vl) cS r2 (P.round - 34) pre a b
      | _, _, _ => False
    else False
  | _, _, _ => False

def finalBad (decodePair : Codec) (P : LiteralTranscript.Prefix) (m : LiteralTranscript.Message)
    (c : LiteralTranscript.Challenge) : Prop :=
  match c.1 with
  | TranscriptView.Value.ordinary v => finalEvent decodePair P m (SelectedChallengeMap.rhoOf v)
  | _ => False

/-- The Aspis classifier on R1's literal carrier. -/
def bad (decodePair : Codec) (P : LiteralTranscript.Prefix) (m : LiteralTranscript.Message)
    (c : LiteralTranscript.Challenge) : Prop :=
  if P.round < 32 then LiteralClassifier.bad P m c
  else if P.round = 32 then
    LiteralOrdinaryDensity.event P m (AspisPairResidual.Row32.bad P) c
  else finalBad decodePair P m c

/-- The Aspis checks on a 40-round transcript: R1's `Checks` fields on the
first 33 rounds except `firstMatch`, `residualBatch` and `pairingChecks`; in
their place the two R1 boundary checks, the batched first-fold equation, and
the final sumcheck's reads and final check. -/
structure AspisChecks (decodePair : Codec) (pub : LiteralTranscript.Public) (rs : Rounds) where
  len : rs.length = 40
  decoded : R0P.Public SemanticPublicWire.M31
  view : LiteralOpeningView.View
  data : MatchingSupport.Data EW
  publicParsed : SemanticPublicWire.parsePublic pub.pubBytes = some decoded
  matchingRead : LiteralMatchingData.read (rs.take 33) = some data
  openingRead : LiteralOpeningView.read (rs.take 33) = some view
  m31 : LiteralTranscript.Message
  queryBytes : List Nat
  state31 : State
  m32 : LiteralTranscript.Message
  rho : EW
  state32 : State
  entry31 : (rs.take 33)[31]? = some (m31,
    (TranscriptView.Value.queries (.ok queryBytes), state31))
  entry32 : (rs.take 33)[32]? = some (m32,
    (TranscriptView.Value.ordinary rho, state32))
  valid31 : LiteralTranscript.valid 31 m31
  valid32 : LiteralTranscript.valid 32 m32
  queries : Fin 22 → Fin 262144
  queryDecode : LiteralQueryRead.decode queryBytes = some queries
  claim : EW
  polynomials : Fin 10 → Polynomial EW
  claimParse : claimOf (SelectedSemanticPrefixFacts.lift view.semantic) = some claim
  polynomialParse : semPolysZ (SelectedSemanticPrefixFacts.lift view.semantic) =
    some polynomials
  semanticChecks : sumcheckChecksZ (maskClaimsR0 ConcretePackBasis.basis)
    (SpendDataMap.mapPublic ExactBaseProjection.embed decoded)
    ConcretePackBasis.basis
    (fun j => (view.semantic.map Prod.snd).getD j.val 0)
    ((view.semantic.map Prod.snd).getD 14 0) claim
    (fun j => (view.semantic.map Prod.snd).getD (15 + j.val) 0) polynomials
    (fun j l => data.Y ⟨j.val, by omega⟩ l) (data.Y 3)
  -- Aspis in place of R1's per-query and pairing checks
  roundBoundaries :
    AspisR1.TwoRoundComparison.boundary data.p1 =
        AspisR1.RoundPairing.quarter * data.p0.eval data.alpha0 ∧
      AspisR1.TwoRoundComparison.boundary data.p0 =
        AspisR1.RoundPairing.quarter *
          AspisR1.JointFunctionalBinding.claimedValue data.Y data.c0 data.gamma data.kappa
  firstBatch : FirstBatch LiteralOpeningView.eK (SelectedChallengeMap.rhoOf rho) data queries
  m33 : LiteralTranscript.Message
  lamV : EW
  state33 : State
  entry33 : rs[33]? = some (m33, (TranscriptView.Value.ordinary lamV, state33))
  claimS : EW
  rhs2 : EW
  decode33 : decodePair m33 = some (claimS, rhs2)
  claimDef : claimS = data.p1.eval data.alpha1
  rhs2Def : rhs2 = rhs2Of LiteralOpeningView.eK (SelectedChallengeMap.rhoOf rho)
    (QueryResidualBridge.values data queries)
  rounds : List (KQ × EW × EW)
  roundsLen : rounds.length = 6
  entryRound : ∀ b (hb : b < 6), ∃ mb vb sb,
    rs[34 + b]? = some (mb, (TranscriptView.Value.ordinary vb, sb)) ∧
    decodePair mb = some ((rounds[b]'(by rw [roundsLen]; exact hb)).2.1,
      (rounds[b]'(by rw [roundsLen]; exact hb)).2.2) ∧
    (rounds[b]'(by rw [roundsLen]; exact hb)).1 = SelectedChallengeMap.rhoOf vb
  finalCheck : FinalCheck LiteralOpeningView.eK rounds claimS rhs2
    (SelectedChallengeMap.rhoOf lamV) (SelectedChallengeMap.rhoOf rho) data queries

/-! ## List helpers -/

theorem hit_exists_index {X M C : Type} (bd : FS.Prefix X M C → M → C → Prop) (x : X) :
    ∀ (rs prev : List (M × C)), GenericNoHit.hitFrom bd x prev rs →
      ∃ i, ∃ hi : i < rs.length, bd ⟨x, prev ++ rs.take i⟩ (rs[i]'hi).1 (rs[i]'hi).2
  | [], _, h => absurd h (by simp [GenericNoHit.hitFrom])
  | (m, c) :: rest, prev, h => by
    simp only [GenericNoHit.hitFrom] at h
    rcases h with h | h
    · exact ⟨0, by simp, by simpa using h⟩
    · obtain ⟨i, hi, hb⟩ := hit_exists_index bd x rest (prev ++ [(m, c)]) h
      refine ⟨i + 1, by simp; omega, ?_⟩
      simpa [List.take_succ_cons, List.append_assoc] using hb

theorem getElem?_take_lt (rs : Rounds) (n i : ℕ) (h : i < n) :
    (rs.take n)[i]? = rs[i]? := by
  simp [List.getElem?_take, h]

theorem getElem_of_getElem? (rs : Rounds) (i : ℕ) (hi : i < rs.length) {x}
    (h : rs[i]? = some x) : rs[i]'hi = x :=
  Option.some.inj ((List.getElem?_eq_getElem hi).symm.trans h)

theorem round_take (pub : LiteralTranscript.Public) (rs : Rounds) (n : ℕ) (h : n ≤ rs.length) :
    (⟨pub, rs.take n⟩ : LiteralTranscript.Prefix).round = n := by
  simp [FS.Prefix.round, h]

/-! ## Reads from the Aspis checks -/

section reads
variable {decodePair : Codec} {pub : LiteralTranscript.Public} {rs : Rounds}

theorem matching32 (c : AspisChecks decodePair pub rs) :
    LiteralMatchingData.read (rs.take 32) = some c.data := by
  have hlen := c.len
  have hstable := LiteralReadStability.matchingData_append_stable
    (rs.take 32) ((rs.take 33).drop 32) (by simp; omega)
  have hdecomp : rs.take 32 ++ (rs.take 33).drop 32 = rs.take 33 := by
    have h1 : (rs.take 33).take 32 = rs.take 32 := by
      rw [List.take_take]; simp
    rw [← h1, List.take_append_drop]
  rw [hdecomp] at hstable
  rw [← hstable]
  exact c.matchingRead

theorem queries32 (c : AspisChecks decodePair pub rs) :
    LiteralQueryRead.queriesAt (rs.take 32) 31 = some c.queries := by
  have h31 : (rs.take 32)[31]? = some (c.m31,
      (TranscriptView.Value.queries (.ok c.queryBytes), c.state31)) := by
    rw [getElem?_take_lt rs 32 31 (by omega), ← getElem?_take_lt rs 33 31 (by omega)]
    exact c.entry31
  simp only [LiteralQueryRead.queriesAt, h31, Option.bind_some]
  exact c.queryDecode

theorem read32 (c : AspisChecks decodePair pub rs) :
    LiteralRhoDensity.read ⟨pub, rs.take 32⟩ = some (c.data, c.queries) := by
  have hlen := c.len
  have hdata : LiteralMatchingData.read (rs.take 32) = some c.data := by
    have hstable := LiteralReadStability.matchingData_append_stable
      (rs.take 32) ((rs.take 33).drop 32) (by simp; omega)
    have hdecomp : rs.take 32 ++ (rs.take 33).drop 32 = rs.take 33 := by
      have h1 : (rs.take 33).take 32 = rs.take 32 := by
        rw [List.take_take]; simp
      rw [← h1, List.take_append_drop]
    rw [hdecomp] at hstable
    rw [← hstable]
    exact c.matchingRead
  have h31 : (rs.take 32)[31]? = some (c.m31,
      (TranscriptView.Value.queries (.ok c.queryBytes), c.state31)) := by
    rw [getElem?_take_lt rs 32 31 (by omega), ← getElem?_take_lt rs 33 31 (by omega)]
    exact c.entry31
  have hq : LiteralQueryRead.queriesAt (rs.take 32) 31 = some c.queries := by
    simp only [LiteralQueryRead.queriesAt, h31, Option.bind_some]
    exact c.queryDecode
  simp only [LiteralRhoDensity.read, LiteralMatchingData.beforeRho, hdata, hq,
    Option.bind_eq_bind]
  rfl

theorem rs32 (c : AspisChecks decodePair pub rs) :
    rs[32]? = some (c.m32, (TranscriptView.Value.ordinary c.rho, c.state32)) := by
  rw [← getElem?_take_lt rs 33 32 (by omega)]
  exact c.entry32

theorem valueAt32 (c : AspisChecks decodePair pub rs) (n : ℕ) (hn : 32 < n) :
    valueAt (rs.take n) 32 = some c.rho := by
  simp [valueAt, getElem?_take_lt rs n 32 hn, rs32 c]

theorem valueAt33 (c : AspisChecks decodePair pub rs) (n : ℕ) (hn : 33 < n) :
    valueAt (rs.take n) 33 = some c.lamV := by
  simp [valueAt, getElem?_take_lt rs n 33 hn, c.entry33]

theorem pair33 (c : AspisChecks decodePair pub rs) (n : ℕ) (hn : 33 < n) :
    ((rs.take n)[33]?).bind (fun mc => decodePair mc.1) = some (c.claimS, c.rhs2) := by
  simp [getElem?_take_lt rs n 33 hn, c.entry33, c.decode33]

theorem roundsAt_take (c : AspisChecks decodePair pub rs) :
    ∀ b, b ≤ 6 → ∀ n, 34 + b ≤ n →
      roundsAt decodePair (rs.take n) b = some (c.rounds.take b)
  | 0, _, _, _ => by simp [roundsAt]
  | b + 1, hb, n, hn => by
    obtain ⟨mb, vb, sb, hentry, hdec, hfst⟩ := c.entryRound b (by omega)
    have ih := roundsAt_take c b (by omega) n (by omega)
    have hv : valueAt (rs.take n) (34 + b) = some vb := by
      simp [valueAt, getElem?_take_lt rs n (34 + b) (by omega), hentry]
    have hm : ((rs.take n)[34 + b]?).bind (fun mc => decodePair mc.1) =
        some ((c.rounds[b]'(by rw [c.roundsLen]; omega)).2.1,
          (c.rounds[b]'(by rw [c.roundsLen]; omega)).2.2) := by
      simp [getElem?_take_lt rs n (34 + b) (by omega), hentry, hdec]
    simp only [roundsAt, ih, hv, hm, Option.bind_some, Option.map_some]
    congr 1
    rw [List.take_succ_eq_append_getElem (by rw [c.roundsLen]; omega)]
    congr 2
    rw [← hfst]

end reads

/-! ## The link, in pieces -/

section link
variable {decodePair : Codec} {pub : LiteralTranscript.Public} {rs : Rounds}

theorem bad_lt32 (P : LiteralTranscript.Prefix) (m : LiteralTranscript.Message)
    (ch : LiteralTranscript.Challenge) (h : P.round < 32) :
    bad decodePair P m ch ↔ LiteralClassifier.bad P m ch := by
  unfold bad
  rw [if_pos h]

theorem bad_eq32 (P : LiteralTranscript.Prefix) (m : LiteralTranscript.Message)
    (ch : LiteralTranscript.Challenge) (h : P.round = 32) :
    bad decodePair P m ch ↔ LiteralOrdinaryDensity.event P m (AspisPairResidual.Row32.bad P) ch := by
  unfold bad
  rw [if_neg (by omega), if_pos h]

theorem bad_ge33 (P : LiteralTranscript.Prefix) (m : LiteralTranscript.Message)
    (ch : LiteralTranscript.Challenge) (h : 33 ≤ P.round) :
    bad decodePair P m ch ↔ finalBad decodePair P m ch := by
  unfold bad
  rw [if_neg (by omega), if_neg (by omega)]

/-- Row 32: no Aspis hit gives `rho ∉ pairBad`. -/
theorem not_pair32 (c : AspisChecks decodePair pub rs)
    (hno : ¬ GenericNoHit.hitFrom (bad decodePair) pub [] rs) :
    SelectedChallengeMap.rhoOf c.rho ∉
      AspisPairResidual.pairBad LiteralOpeningView.eK c.data c.queries := by
  have hlen := c.len
  intro hin
  have h := GenericNoHitIndex.not_bad_at_index (bad decodePair) pub rs 32 (by omega) hno
  rw [getElem_of_getElem? rs 32 (by omega) (rs32 c)] at h
  apply h
  rw [bad_eq32 _ _ _ (round_take pub rs 32 (by omega))]
  unfold LiteralOrdinaryDensity.event AspisPairResidual.Row32.bad
  refine ⟨by rw [round_take pub rs 32 (by omega)]; exact c.valid32, ?_⟩
  change (match LiteralRhoDensity.read ⟨pub, rs.take 32⟩ with
    | none => False
    | some (d, q) => SelectedChallengeMap.rhoOf c.rho ∈
        AspisPairResidual.pairBad LiteralOpeningView.eK d q)
  rw [read32 c]
  exact hin

/-- Row 33: no Aspis hit gives `λ ∉ lambdaBad`. -/
theorem not_lam33 (c : AspisChecks decodePair pub rs)
    (hno : ¬ GenericNoHit.hitFrom (bad decodePair) pub [] rs) :
    SelectedChallengeMap.rhoOf c.lamV ∉ lamBadSet LiteralOpeningView.eK c.data c.queries
      (SelectedChallengeMap.rhoOf c.rho) c.claimS c.rhs2 := by
  have hlen := c.len
  intro hin
  have h := GenericNoHitIndex.not_bad_at_index (bad decodePair) pub rs 33 (by omega) hno
  rw [getElem_of_getElem? rs 33 (by omega) c.entry33] at h
  apply h
  rw [bad_ge33 _ _ _ (by rw [round_take pub rs 33 (by omega)])]
  unfold finalBad
  change finalEvent decodePair ⟨pub, rs.take 33⟩ c.m33 (SelectedChallengeMap.rhoOf c.lamV)
  have hr : (rs.take 33).take 32 = rs.take 32 := by rw [List.take_take]; simp
  unfold finalEvent
  change (match LiteralRhoDensity.read ⟨pub, (rs.take 33).take 32⟩, valueAt (rs.take 33) 32,
      decodePair c.m33 with
    | some (d, q), some vr, some (a, b) =>
      if (⟨pub, rs.take 33⟩ : LiteralTranscript.Prefix).round = 33 then
        SelectedChallengeMap.rhoOf c.lamV ∈
          lamBadSet LiteralOpeningView.eK d q (SelectedChallengeMap.rhoOf vr) a b
      else if (⟨pub, rs.take 33⟩ : LiteralTranscript.Prefix).round < 40 then
        match valueAt (rs.take 33) 33, ((rs.take 33)[33]?).bind (fun mc => decodePair mc.1),
            roundsAt decodePair (rs.take 33)
              ((⟨pub, rs.take 33⟩ : LiteralTranscript.Prefix).round - 34) with
        | some vl, some (cS, r2), some pre =>
            SelectedChallengeMap.rhoOf c.lamV ∈ roundBadSet LiteralOpeningView.eK d q
              (SelectedChallengeMap.rhoOf vr) (SelectedChallengeMap.rhoOf vl) cS r2
              ((⟨pub, rs.take 33⟩ : LiteralTranscript.Prefix).round - 34) pre a b
        | _, _, _ => False
      else False
    | _, _, _ => False)
  rw [hr, read32 c, valueAt32 c 33 (by omega), c.decode33, round_take pub rs 33 (by omega)]
  exact hin

theorem not_rounds (c : AspisChecks decodePair pub rs)
    (hno : ¬ GenericNoHit.hitFrom (bad decodePair) pub [] rs) :
    ∀ b (hb : b < c.rounds.length),
      (c.rounds[b]'hb).1 ∉ roundBadSet LiteralOpeningView.eK c.data c.queries
        (SelectedChallengeMap.rhoOf c.rho) (SelectedChallengeMap.rhoOf c.lamV) c.claimS c.rhs2 b
        (c.rounds.take b) (c.rounds[b]'hb).2.1 (c.rounds[b]'hb).2.2 := by
  have hlen := c.len
  intro b hb hin
  have hb6 : b < 6 := by rw [← c.roundsLen]; exact hb
  obtain ⟨mb, vb, sb, hentry, hdec, hfst⟩ := c.entryRound b hb6
  have h := GenericNoHitIndex.not_bad_at_index (bad decodePair) pub rs (34 + b) (by omega) hno
  rw [getElem_of_getElem? rs (34 + b) (by omega) hentry] at h
  apply h
  rw [bad_ge33 _ _ _ (by rw [round_take pub rs (34 + b) (by omega)]; omega)]
  unfold finalBad
  change finalEvent decodePair ⟨pub, rs.take (34 + b)⟩ mb (SelectedChallengeMap.rhoOf vb)
  have hr : (rs.take (34 + b)).take 32 = rs.take 32 := by
    rw [List.take_take, Nat.min_eq_left (by omega)]
  have hsub : 34 + b - 34 = b := by omega
  unfold finalEvent
  change (match LiteralRhoDensity.read ⟨pub, (rs.take (34 + b)).take 32⟩,
      valueAt (rs.take (34 + b)) 32, decodePair mb with
    | some (d, q), some vr, some (a, b') =>
      if (⟨pub, rs.take (34 + b)⟩ : LiteralTranscript.Prefix).round = 33 then
        SelectedChallengeMap.rhoOf vb ∈
          lamBadSet LiteralOpeningView.eK d q (SelectedChallengeMap.rhoOf vr) a b'
      else if (⟨pub, rs.take (34 + b)⟩ : LiteralTranscript.Prefix).round < 40 then
        match valueAt (rs.take (34 + b)) 33,
            ((rs.take (34 + b))[33]?).bind (fun mc => decodePair mc.1),
            roundsAt decodePair (rs.take (34 + b))
              ((⟨pub, rs.take (34 + b)⟩ : LiteralTranscript.Prefix).round - 34) with
        | some vl, some (cS, r2), some pre =>
            SelectedChallengeMap.rhoOf vb ∈ roundBadSet LiteralOpeningView.eK d q
              (SelectedChallengeMap.rhoOf vr) (SelectedChallengeMap.rhoOf vl) cS r2
              ((⟨pub, rs.take (34 + b)⟩ : LiteralTranscript.Prefix).round - 34) pre a b'
        | _, _, _ => False
      else False
    | _, _, _ => False)
  rw [hr, read32 c, valueAt32 c (34 + b) (by omega), hdec, round_take pub rs (34 + b) (by omega),
    valueAt33 c (34 + b) (by omega), pair33 c (34 + b) (by omega), hsub,
    roundsAt_take c b (by omega) (34 + b) (by omega)]
  dsimp only
  rw [if_neg (by omega), if_pos (by omega)]
  rw [← hfst]
  exact hin

/-- R1's no-hit on the first 33 rounds, given the second-fold residuals vanish. -/
theorem r1_noHit33 (c : AspisChecks decodePair pub rs)
    (hno : ¬ GenericNoHit.hitFrom (bad decodePair) pub [] rs)
    (hres : ∀ i, QueryResidualBridge.residuals c.data c.queries i = 0) :
    ¬ GenericNoHit.hitFrom LiteralClassifier.bad pub [] (rs.take 33) := by
  have hlen := c.len
  intro hhit
  obtain ⟨i, hi, hbad⟩ := hit_exists_index LiteralClassifier.bad pub (rs.take 33) [] hhit
  have hi33 : i < 33 := by rw [List.length_take] at hi; omega
  have htk : (rs.take 33).take i = rs.take i := by rw [List.take_take]; congr 1; omega
  have hget : (rs.take 33)[i]'hi = rs[i]'(by omega) := by simp
  rw [List.nil_append, htk, hget] at hbad
  by_cases h32 : i < 32
  · have h := GenericNoHitIndex.not_bad_at_index (bad decodePair) pub rs i (by omega) hno
    rw [bad_lt32 _ _ _ (by rw [round_take pub rs i (by omega)]; exact h32)] at h
    exact h hbad
  · obtain rfl : i = 32 := by omega
    rw [getElem_of_getElem? rs 32 (by omega) (rs32 c)] at hbad
    have hiff := LiteralRhoBinding.rho_event_iff ⟨pub, rs.take 32⟩ c.m32 c.rho c.state32 c.data
      c.queries (round_take pub rs 32 (by omega)) c.valid32 (matching32 c) (queries32 c)
    have hz : ResidualBatch.residualPolynomial (QueryResidualBridge.residuals c.data c.queries) = 0 := by
      unfold ResidualBatch.residualPolynomial
      simp only [hres, map_zero, Finset.sum_const_zero]
    have hempty : QueryResidualBridge.rhoBad LiteralOpeningView.eK c.data c.queries = ∅ := by
      unfold QueryResidualBridge.rhoBad ResidualBatch.bad
      rw [if_pos hz]
    have hin := hiff.mp hbad
    rw [hempty] at hin
    simp at hin

theorem accepted_of (c : AspisChecks decodePair pub rs)
    (hdot : AspisR1.RoundPairing.dot c.data.f (relW c.data) = c.claimS) :
    MatchingSupport.AcceptedPairing c.data := by
  unfold MatchingSupport.AcceptedPairing
  exact ⟨c.claimDef.symm.trans hdot.symm, c.roundBoundaries.1, c.roundBoundaries.2⟩

theorem pairing_of (c : AspisChecks decodePair pub rs)
    (hdot : AspisR1.RoundPairing.dot c.data.f (relW c.data) = c.claimS) :
    LiteralPairingChecks.checks (rs.take 33) :=
  (LiteralPairingChecks.acceptedPairing_iff_checks (rs.take 33) c.data
    c.matchingRead).mp (accepted_of c hdot)

theorem batch_of (c : AspisChecks decodePair pub rs)
    (hres : ∀ i, QueryResidualBridge.residuals c.data c.queries i = 0) :
    ∑ j : Fin 22,
      (LiteralOpeningView.eK (SelectedChallengeMap.rhoOf c.rho)) ^ j.val *
        QueryResidualBridge.residuals c.data c.queries j = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  rw [hres j, mul_zero]

/-- R1's `Checks` on the first 33 rounds, from the Aspis checks and the three
conclusions of the model link. -/
theorem checks_of (c : AspisChecks decodePair pub rs)
    (hdot : AspisR1.RoundPairing.dot c.data.f (relW c.data) = c.claimS)
    (hmatch : ∀ i, MatchingSupport.match0 c.data (c.queries i))
    (hres : ∀ i, QueryResidualBridge.residuals c.data c.queries i = 0) :
    Nonempty (LiteralAcceptanceTerminal.Checks pub (rs.take 33)) :=
  ⟨LiteralAcceptanceTerminal.Checks.mk c.decoded c.view c.data
    c.publicParsed c.matchingRead c.openingRead (pairing_of c hdot)
    c.m31 c.queryBytes c.state31 c.m32 c.rho c.state32
    c.entry31 c.entry32 c.valid31 c.valid32
    c.queries c.queryDecode hmatch
    (by apply Finset.sum_eq_zero; intro j _; simp only [hres j, mul_zero])
    c.claim c.polynomials c.claimParse c.polynomialParse c.semanticChecks⟩

end link


/-! ## The link -/

theorem aspis_checks_noHit_r1_checks (decodePair : Codec) (pub : LiteralTranscript.Public)
    (rs : Rounds) (c : AspisChecks decodePair pub rs)
    (hno : ¬ GenericNoHit.hitFrom (bad decodePair) pub [] rs) :
    Nonempty (LiteralAcceptanceTerminal.Checks pub (rs.take 33)) ∧
      ¬ GenericNoHit.hitFrom LiteralClassifier.bad pub [] (rs.take 33) := by
  have hfinal := c.finalCheck
  have hlam := not_lam33 c hno
  have hrounds := not_rounds c hno
  rw [c.rhs2Def] at hfinal hlam hrounds
  obtain ⟨hdot, hmatch, hres⟩ := link_model LiteralOpeningView.eK c.data c.queries
    (SelectedChallengeMap.rhoOf c.rho) (SelectedChallengeMap.rhoOf c.lamV) c.claimS c.rounds
    c.roundsLen c.firstBatch hfinal (not_pair32 c hno) hlam hrounds
  exact ⟨checks_of c hdot hmatch hres, r1_noHit33 c hno hres⟩

/-- With R1's terminal theorem: the Aspis checks and no Aspis hit give a
witness of R1's spend relation, provided the first 33 rounds are R1's
transcript (`hprefix`; supplied by `AspisRows40.Literal.transcript_take33`,
see `AspisAcceptanceLinkR40`). -/
theorem aspis_relation_of_checks (decodePair : Codec) (decoder : LiteralByteProtocol.Decoder)
    (H : LiteralByteProtocol.Address → LiteralByteProtocol.State)
    (pub : LiteralTranscript.Public) (pf : LiteralByteProtocol.Proof) (rs : Rounds)
    (hprefix : rs.take 33 =
      ((LiteralByteProtocol.protocol decoder).transcript H pub pf 33).rounds)
    (c : AspisChecks decodePair pub rs)
    (hno : ¬ GenericNoHit.hitFrom (bad decodePair) pub [] rs) :
    ∃ w, LiteralProtocol.relation pub w := by
  obtain ⟨⟨checks⟩, hno33⟩ := aspis_checks_noHit_r1_checks decodePair pub rs c hno
  rw [hprefix] at checks hno33
  exact LiteralAcceptanceTerminal.checks_noHit_relation decoder H pub pf checks hno33

#print axioms hit_exists_index
#print axioms read32
#print axioms roundsAt_take
#print axioms not_pair32
#print axioms not_lam33
#print axioms not_rounds
#print axioms r1_noHit33
#print axioms checks_of
#print axioms aspis_checks_noHit_r1_checks
#print axioms aspis_relation_of_checks
end AspisAcceptance
end
