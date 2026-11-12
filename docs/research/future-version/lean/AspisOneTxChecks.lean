import AspisOneTxDecision
import OraclePortFrozenOrderChecks
import AspisPairResidualObservation

/-! The Aspis one-transaction verifier: the selected-checks structure (item M8)
and accepted ⇒ `AspisChecks` on a containing log (the Aspis copy of R1's
`OraclePortFrozenOrderChecks.accepted_checks`) of ONE-TRANSACTION-GAME.md.

Kind of result: MODEL THEOREMS in R1's stored-decision and binary commitment
model. The chain is R1's, step for step:
* `SelChecks` is R1's `OraclePortSelectedConsumerC6.Checks` with `writer`
  (per-query first fold) and `backend` (first pairing conjunct and the closed
  second-fold sum) replaced by R1's two boundary conjuncts, the batched
  first-fold equation and the final sumcheck (`FinalPart`), and 40 rounds;
* `ofTypedS` is R1's `ofTyped` for `verifyS`;
* `transportS` is R1's `transport` (same three agreement premises, R1's
  `observe_withWords` for the semantic part, the pair-binding agent's
  `pair_withWords` for the batched first-fold equation; rows 33..39 are
  untouched by enrichment);
* `toAspisChecks` is R1's `toLiteral_nonempty` with the target the acceptance
  link's `AspisChecks` at the codec `decodePairS`;
* `accepted_checks_aspis` is R1's containing-log `accepted_checks` for
  `dV_aspis`, with R1's `authenticated` replaced by `authenticated_merged`.
The exceptional event is R1's `AllAddressCollision.bad iv
BinRawByteCollisionTargets.pred Q`, unchanged.

NOT established here: the identification of the containing log, frames and
root reads with the actual 40-row run (item M7), which needs the 40-row
oracle-decision experiment; the source refinement of `dV_aspis`. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
noncomputable section
namespace AspisOneTx
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open AspisR1 AspisR1.OraclePortCompactDraft AspisR1.OraclePortSelectedDraft AspisR1.OraclePortBatchDraft
open AspisR1.OraclePortStoredDecisionDraftC4 AspisR1.OraclePortReaderPlumbingC6
open AspisR1.OraclePortSelectedObservationsC6
open AspisR1.OraclePortSelectedArithmeticC4 (withWords)
open AspisFuture.StageD
open AspisAcceptance (EW KQ Rounds Codec FirstBatch FinalCheck AspisChecks)
open RawCutTranscriptRun (ErasedPrefix ErasedMessage)
open RecordedBinaryExperimentBin (SourceInputs)
attribute [local irreducible] LiteralTypedWords.word MatchingSupport.match0
  MatchingSupport.AcceptedPairing QueryResidualBridge.values QueryResidualBridge.basis

/-- The Aspis selected checks (copy of `OraclePortSelectedConsumerC6.Checks`). -/
structure SelChecks (pub : LiteralTranscript.Public) (rs : Rounds) where
  len : rs.length = 40
  decoded : R0P.Public SemanticPublicWire.M31
  data : MatchingSupport.Data EW
  view : LiteralOpeningView.View
  publicParsed : SemanticPublicWire.parsePublic pub.pubBytes = some decoded
  matchingRead : LiteralMatchingData.read (rs.take 33) = some data
  openingRead : LiteralOpeningView.read (rs.take 33) = some view
  m31 : LiteralTranscript.Message
  queryBytes : List Nat
  state31 : State
  m32 : LiteralTranscript.Message
  rho : EW
  state32 : State
  entry31 : (rs.take 33)[31]? = some (m31,(TranscriptView.Value.queries (.ok queryBytes),state31))
  entry32 : (rs.take 33)[32]? = some (m32,(TranscriptView.Value.ordinary rho,state32))
  valid31 : LiteralTranscript.valid 31 m31
  valid32 : LiteralTranscript.valid 32 m32
  queries : Fin 22 → Fin 262144
  queryDecode : LiteralQueryRead.decode queryBytes = some queries
  boundaries : Boundaries data
  firstBatch : FirstBatch LiteralOpeningView.eK (SelectedChallengeMap.rhoOf rho) data queries
  semantic : OraclePortSelectedConsumerC6.Semantic decoded (observe data queries)
    (OraclePortSemanticProjectionC6.observe view.semantic)
  final : FinalPart rs data queries (SelectedChallengeMap.rhoOf rho)

/-- Copy of R1's `OraclePortObservationTransportC6.ofTyped`. -/
theorem ofTypedS (pub : LiteralTranscript.Public) (rs : Rounds) (i : SourceInputs)
    (q : Fin 22 → Fin 262144) (hlen : rs.length = 40)
    (publicParsed : SemanticPublicWire.parsePublic pub.pubBytes = some i.decoded)
    (row31 : (rs.take 33)[31]? = some (i.m31,(TranscriptView.Value.queries (.ok i.queryBytes),i.state31)))
    (row32 : (rs.take 33)[32]? = some (i.m32,(TranscriptView.Value.ordinary i.rho,i.state32)))
    (valid31 : LiteralTranscript.valid 31 i.m31) (valid32 : LiteralTranscript.valid 32 i.m32)
    (decoded : LiteralQueryRead.decode i.queryBytes = some q)
    (accepted : verifyS rs i = true) :
    Nonempty (SelChecks pub rs) := by
  obtain ⟨matching, bnd, equations, rest⟩ := verifyS_accepted rs i accepted
  obtain ⟨v, claim, polys, hopen, hclaim, hpolys⟩ :=
    HchecksReaderComposition.matching_read_parsers (rs.take 33) i.data matching
  obtain ⟨fb, fp⟩ := rest q decoded
  exact ⟨{
    len := hlen, decoded := i.decoded, data := i.data, view := v
    publicParsed := publicParsed, matchingRead := matching, openingRead := hopen
    m31 := i.m31, queryBytes := i.queryBytes, state31 := i.state31
    m32 := i.m32, rho := i.rho, state32 := i.state32
    entry31 := row31, entry32 := row32, valid31 := valid31, valid32 := valid32
    queries := q, queryDecode := decoded
    boundaries := bnd, firstBatch := fb
    semantic := (OraclePortSelectedConsumerC6.semantic_iff i.decoded i.data q v claim polys
      hclaim hpolys).2 (equations v claim polys hopen hclaim hpolys)
    final := fp }⟩

/-! Generic facts over abstract words: word replacement changes none of the
scalar fields these checks read. Stated with variables and proved by rewriting
with projection lemmas, so that no concrete word or field instance is unfolded. -/
section words
variable (dd : MatchingSupport.Data EW)
  (W : Fin 29 → AspisPool.AlgorithmicCircleDecoderV7.InitialWord EW)
  (V : AspisPool.AlgorithmicCircleDecoderV7.FinalWord EW)

theorem f_ww : (withWords dd W V).f = dd.f := rfl
theorem p0_ww : (withWords dd W V).p0 = dd.p0 := rfl
theorem p1_ww : (withWords dd W V).p1 = dd.p1 := rfl
theorem alpha0_ww : (withWords dd W V).alpha0 = dd.alpha0 := rfl
theorem alpha1_ww : (withWords dd W V).alpha1 = dd.alpha1 := rfl
theorem Y_ww : (withWords dd W V).Y = dd.Y := rfl
theorem c0_ww : (withWords dd W V).c0 = dd.c0 := rfl
theorem gamma_ww : (withWords dd W V).gamma = dd.gamma := rfl
theorem kappa_ww : (withWords dd W V).kappa = dd.kappa := rfl
theorem F_ww : (withWords dd W V).F = dd.F := rfl
theorem F0_ww : (withWords dd W V).F0 = dd.F0 := rfl

theorem observe_second (q : Fin 22 → Fin 262144) :
    (observe dd q).second = QueryResidualBridge.values dd q := by
  unfold observe; rfl

theorem bnd_ww : Boundaries (withWords dd W V) = Boundaries dd := by
  unfold Boundaries
  rw [p0_ww, p1_ww, alpha0_ww, Y_ww, c0_ww, gamma_ww, kappa_ww]

theorem fin_ww (rounds : List (KQ × EW × EW)) (claimS rhs2 : EW) (lam rho : KQ)
    (q : Fin 22 → Fin 262144) :
    FinalCheck LiteralOpeningView.eK rounds claimS rhs2 lam rho (withWords dd W V) q =
      FinalCheck LiteralOpeningView.eK rounds claimS rhs2 lam rho dd q := by
  unfold AspisAcceptance.FinalCheck AspisAcceptance.relW
  rw [f_ww, alpha0_ww, alpha1_ww, F_ww, F0_ww, kappa_ww]
end words

theorem values_ww (dd : MatchingSupport.Data EW)
    (W : Fin 29 → AspisPool.AlgorithmicCircleDecoderV7.InitialWord EW)
    (V : AspisPool.AlgorithmicCircleDecoderV7.FinalWord EW) (q : Fin 22 → Fin 262144)
    (same : observe dd q = observe (withWords dd W V) q) :
    QueryResidualBridge.values dd q = QueryResidualBridge.values (withWords dd W V) q := by
  rw [← observe_second, ← observe_second, same]

section generic
variable {K E : Type} [Field K] [Field E] [Fintype E] [DecidableEq E]
  [Algebra (ZMod AspisCircleGroupOrder.P) E]

/-- Generic in the fields, so that no concrete field instance is unfolded. -/
theorem firstBatch_congr (iota : K →+* E) (rho : K) (d d' : MatchingSupport.Data E)
    (q : Fin 22 → Fin 262144)
    (h0 : AspisPairResidual.firstResiduals d q = AspisPairResidual.firstResiduals d' q)
    (h : FirstBatch iota rho d q) : FirstBatch iota rho d' q := by
  unfold AspisAcceptance.FirstBatch at h ⊢
  rw [← h0]
  exact h
end generic

theorem firstBatch_ww (dd : MatchingSupport.Data EW)
    (W : Fin 29 → AspisPool.AlgorithmicCircleDecoderV7.InitialWord EW)
    (V : AspisPool.AlgorithmicCircleDecoderV7.FinalWord EW) (q : Fin 22 → Fin 262144) (rho : KQ)
    (pair1 : AspisPairResidual.firstResiduals dd q = AspisPairResidual.firstResiduals (withWords dd W V) q)
    (h : FirstBatch LiteralOpeningView.eK rho dd q) :
    FirstBatch LiteralOpeningView.eK rho (withWords dd W V) q :=
  firstBatch_congr LiteralOpeningView.eK rho dd (withWords dd W V) q pair1 h

theorem finalPart_ww (rs : Rounds) (w : CanonicalCutEnrichedTranscript.Words)
    (dd : MatchingSupport.Data EW)
    (W : Fin 29 → AspisPool.AlgorithmicCircleDecoderV7.InitialWord EW)
    (V : AspisPool.AlgorithmicCircleDecoderV7.FinalWord EW) (q : Fin 22 → Fin 262144) (rho : KQ)
    (hv : QueryResidualBridge.values dd q = QueryResidualBridge.values (withWords dd W V) q)
    (h : FinalPart rs dd q rho) : FinalPart (reword w rs) (withWords dd W V) q rho := by
  obtain ⟨m33, lamV, st33, cS, r2, rounds, hlen6, e33, d33, cdef, rdef, hround, hfin⟩ := h
  refine ⟨CanonicalCutEnrichedTranscript.enrichMessage w m33, lamV, st33, cS, r2, rounds, hlen6,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [reword,List.getElem?_map,e33,Option.map_some]
  · rw [decodePairS_enrich]; exact d33
  · rw [p1_ww, alpha1_ww]; exact cdef
  · rw [← hv]; exact rdef
  · intro b hb
    obtain ⟨mb, vb, sb, eb, db, rb⟩ := hround b hb
    exact ⟨CanonicalCutEnrichedTranscript.enrichMessage w mb, vb, sb,
      by simp only [reword,List.getElem?_map,eb,Option.map_some],
      by rw [decodePairS_enrich]; exact db, rb⟩
  · rw [fin_ww]; exact hfin

theorem late_rows (w : CanonicalCutEnrichedTranscript.Words) (rs : Rounds)
    (m31 m32 : LiteralTranscript.Message) (queryBytes : List Nat) (state31 state32 : State) (rho : EW)
    (entry31 : (rs.take 33)[31]? = some (m31,(TranscriptView.Value.queries (.ok queryBytes),state31)))
    (entry32 : (rs.take 33)[32]? = some (m32,(TranscriptView.Value.ordinary rho,state32)))
    (valid31 : LiteralTranscript.valid 31 m31) (valid32 : LiteralTranscript.valid 32 m32) :
    ((reword w rs).take 33)[31]? = some (m31,(TranscriptView.Value.queries (.ok queryBytes),state31)) ∧
    ((reword w rs).take 33)[32]? = some (m32,(TranscriptView.Value.ordinary rho,state32)) := by
  have late31 : CanonicalCutEnrichedTranscript.enrichMessage w m31 = m31 :=
    D0InstanceAdmission.valid_payload_injective 31 (by decide) (by decide) (by decide) _ _
      ((OraclePortSemanticObservationsC6.valid_enrich w 31 m31).2 valid31) valid31 (erased w m31)
  have late32 : CanonicalCutEnrichedTranscript.enrichMessage w m32 = m32 :=
    D0InstanceAdmission.valid_payload_injective 32 (by decide) (by decide) (by decide) _ _
      ((OraclePortSemanticObservationsC6.valid_enrich w 32 m32).2 valid32) valid32 (erased w m32)
  rw [reword_take]
  exact ⟨by simp only [reword,List.getElem?_map,entry31,Option.map_some,late31],
    by simp only [reword,List.getElem?_map,entry32,Option.map_some,late32]⟩

/-- The transport step over abstract replacement words `W`, `V`. -/
theorem transport_core (pub : LiteralTranscript.Public) (rs : Rounds) (c : SelChecks pub rs)
    (w : CanonicalCutEnrichedTranscript.Words)
    (W : Fin 29 → AspisPool.AlgorithmicCircleDecoderV7.InitialWord EW)
    (V : AspisPool.AlgorithmicCircleDecoderV7.FinalWord EW)
    (matching : LiteralMatchingData.read ((reword w rs).take 33) = some (withWords c.data W V))
    (v : LiteralOpeningView.View)
    (hopen : LiteralOpeningView.read ((reword w rs).take 33) = some v)
    (semantic : OraclePortSemanticProjectionC6.observe v.semantic =
      OraclePortSemanticProjectionC6.observe c.view.semantic)
    (same : observe c.data c.queries = observe (withWords c.data W V) c.queries)
    (pair1 : AspisPairResidual.firstResiduals c.data c.queries =
      AspisPairResidual.firstResiduals (withWords c.data W V) c.queries) :
    Nonempty (SelChecks pub (reword w rs)) := by
  have rows := late_rows w rs c.m31 c.m32 c.queryBytes c.state31 c.state32 c.rho
    c.entry31 c.entry32 c.valid31 c.valid32
  have fb := firstBatch_ww c.data W V c.queries (SelectedChallengeMap.rhoOf c.rho) pair1 c.firstBatch
  have bnd : Boundaries (withWords c.data W V) := by
    rw [bnd_ww]; exact c.boundaries
  have sem : OraclePortSelectedConsumerC6.Semantic c.decoded (observe (withWords c.data W V) c.queries)
      (OraclePortSemanticProjectionC6.observe v.semantic) := by
    rw [← same,semantic]; exact c.semantic
  have final' := finalPart_ww rs w c.data W V c.queries (SelectedChallengeMap.rhoOf c.rho)
    (values_ww c.data W V c.queries same) c.final
  have len : (reword w rs).length = 40 := by
    simp only [reword,List.length_map]; exact c.len
  exact ⟨⟨len, c.decoded, withWords c.data W V, v, c.publicParsed, matching, hopen,
    c.m31, c.queryBytes, c.state31, c.m32, c.rho, c.state32, rows.1, rows.2,
    c.valid31, c.valid32, c.queries, c.queryDecode, bnd, fb, sem, final'⟩⟩

/-- Copy of R1's `OraclePortObservationTransportC6.transport`: the checks carry
to any words that agree on the selected initial fibres, the selected folded
values and the selected folded fibres. -/
theorem transportS (pub : LiteralTranscript.Public) (rs : Rounds) (c : SelChecks pub rs)
    (w : CanonicalCutEnrichedTranscript.Words)
    (initial : ∀ j lane, FirstFold.fibre (c.data.W lane) (c.queries j) =
      FirstFold.fibre ((LiteralTypedWords.word ExactBaseProjection.embed LiteralOpeningView.eK w.c1 w.c2) lane)
        (c.queries j))
    (opened : ∀ j, c.data.V (c.queries j) = w.final (c.queries j))
    (folded : ∀ j slot, c.data.V (childIndex (n := 65536) (parentIndex (n := 65536) (c.queries j)) slot) =
      w.final (childIndex (n := 65536) (parentIndex (n := 65536) (c.queries j)) slot)) :
    Nonempty (SelChecks pub (reword w rs)) := by
  have matching := OraclePortMatchingRewordC6.matching w (rs.take 33) c.data c.matchingRead
  rw [← reword_take] at matching
  obtain ⟨v,hopen,_,_,_,_,_⟩ := OraclePortOpeningRewordC6.opening w (rs.take 33) c.view c.openingRead
  have semantic := OraclePortMatchingRewordC6.semantic w (rs.take 33) c.view v c.openingRead hopen
  rw [← reword_take] at hopen
  exact transport_core pub rs c w _ _ matching v hopen semantic
    (observe_withWords c.data _ w.final c.queries initial opened folded)
    (AspisPairResidual.pair_withWords c.data _ w.final c.queries initial opened folded).1

/-- Copy of R1's `OraclePortSelectedConsumerC6.toLiteral_nonempty`, targeting
the acceptance link's `AspisChecks` at the codec `decodePairS`. -/
theorem toAspisChecks {pub : LiteralTranscript.Public} {rs : Rounds} (c : SelChecks pub rs) :
    Nonempty (AspisChecks decodePairS pub rs) := by
  obtain ⟨v, claim, polys, hopen, hclaim, hpolys⟩ :=
    HchecksReaderComposition.matching_read_parsers (rs.take 33) c.data c.matchingRead
  have vsame : v = c.view := Option.some.inj (hopen.symm.trans c.openingRead)
  subst vsame
  have equations : R3SemanticRemainingJoins.EquationEndpoint c.decoded (rs.take 33) c.data := by
    intro v' claim' polys' hopen' hclaim' hpolys'
    have same : v' = c.view := Option.some.inj (hopen'.symm.trans c.openingRead)
    subst same
    exact (OraclePortSelectedConsumerC6.semantic_iff c.decoded c.data c.queries c.view claim' polys'
      hclaim' hpolys').1 c.semantic
  have semanticChecks := R3SemanticRemainingJoins.semantic_of_equations c.decoded (rs.take 33) c.data
    equations c.view claim polys hopen hclaim hpolys
  obtain ⟨m33, lamV, st33, cS, r2, rounds, hlen6, e33, d33, cdef, rdef, hround, hfin⟩ := c.final
  exact ⟨{
    len := c.len, decoded := c.decoded, view := c.view, data := c.data
    publicParsed := c.publicParsed, matchingRead := c.matchingRead, openingRead := c.openingRead
    m31 := c.m31, queryBytes := c.queryBytes, state31 := c.state31
    m32 := c.m32, rho := c.rho, state32 := c.state32
    entry31 := c.entry31, entry32 := c.entry32, valid31 := c.valid31, valid32 := c.valid32
    queries := c.queries, queryDecode := c.queryDecode
    claim := claim, polynomials := polys, claimParse := hclaim, polynomialParse := hpolys
    semanticChecks := semanticChecks
    roundBoundaries := c.boundaries
    firstBatch := c.firstBatch
    m33 := m33, lamV := lamV, state33 := st33, entry33 := e33
    claimS := cS, rhs2 := r2, decode33 := d33, claimDef := cdef, rhs2Def := rdef
    rounds := rounds, roundsLen := hlen6, entryRound := hround, finalCheck := hfin }⟩

/-! ### Accepted ⇒ AspisChecks on a containing log -/

theorem typedRows_take (p : Parsed) (q : Fin 22 → Fin 262144) (tr : ErasedPrefix) :
    (typedRows p q tr).take 33 = typedRows p q (take33 tr) := by
  apply List.ext_getElem?
  intro n
  by_cases h : n < 33 <;>
    simp [typedRows, take33, List.getElem?_mapIdx, h]

/-- Copy of R1's `OraclePortFrozenOrderChecks.accepted_checks` for the Aspis
decision: an accepted `dV_aspis` run whose merged-multiproof reads lie in a
clean log with the three root frames read gives `AspisChecks` on the typed
rows carrying the words recovered from that log. -/
theorem accepted_checks_aspis (H : Bytes → State) (stored : Bytes)
    (tr : ErasedPrefix) (m : ErasedMessage)
    (p : Parsed) (q : Fin 22 → Fin 262144)
    (parsed : parseReachedS stored tr = some p)
    (query : queries (take33 tr) = some q)
    (accepted : (eval H (dV_aspis stored tr m)).2 = true)
    (log : List (Bytes × State)) (Q : Nat)
    (consistent : ∀ a ∈ log, a.2 = H a.1)
    (contains : ∀ a, Read (eval H (verifyMergedAll p q)).1 a → Read log a)
    (bound : firstReads emptyTable log ≤ Q)
    (clean : ¬ hitsBad (AllAddressCollision.bad SelectedTranscriptParams.params.iv
      BinRawByteCollisionTargets.pred Q) emptyTable log)
    (frames : Fin 3 → Bytes) (selectors : Fin 3 → Fin 5)
    (frameRead : ∀ k, Read log (frames k))
    (rootRead : ∀ k, BinRawByteCollisionTargets.pred (selectors k) (frames k) =
      some (committedRoot p k.val)) :
    Nonempty (AspisChecks decodePairS tr.statement
      (reword (OraclePortFrozenOrderChecks.maps log frames p) (typedRows p q tr))) := by
  obtain ⟨_,len40,p',q',i,hp,hq,merkle,input,checked⟩ :=
    accepted_detailsS stored tr m H accepted
  have psame : p' = p := Option.some.inj (hp.symm.trans parsed)
  have qsame : q' = q := Option.some.inj (hq.symm.trans query)
  subst p'; subst q'
  have fields := (input_fields p q (take33 tr) i input).1
  have decoded : LiteralQueryRead.decode i.queryBytes = some q := by
    simpa [queries,fields.2.1] using query
  have row31 : (typedRows p q (take33 tr))[31]? = some (i.m31,
      (TranscriptView.Value.queries (.ok i.queryBytes),i.state31)) := by
    rw [typedRows,List.getElem?_mapIdx,fields.2.1]
    simp only [Option.map_some,OraclePortCandidateChecksC4.restore_late _ 31
      (by decide) (by decide) (by decide) _ fields.2.2.2.1]
  have row32 : (typedRows p q (take33 tr))[32]? = some (i.m32,
      (TranscriptView.Value.ordinary i.rho,i.state32)) := by
    rw [typedRows,List.getElem?_mapIdx,fields.2.2.1]
    simp only [Option.map_some,OraclePortCandidateChecksC4.restore_late _ 32
      (by decide) (by decide) (by decide) _ fields.2.2.2.2]
  have hlen : (typedRows p q tr).length = 40 := by
    simp only [typedRows,List.length_mapIdx]; exact len40
  rw [← typedRows_take] at row31 row32
  obtain ⟨c⟩ := ofTypedS tr.statement (typedRows p q tr) i q hlen
    fields.1 row31 row32 fields.2.2.2.1 fields.2.2.2.2 decoded checked
  have matching : LiteralMatchingData.read (typedRows p q (take33 tr)) = some i.data := by
    rw [← typedRows_take]; exact (verifyS_accepted _ i checked).1
  have dataSame : c.data = i.data := by
    have h := c.matchingRead
    rw [typedRows_take] at h
    exact Option.some.inj (h.symm.trans matching)
  have tags := congrArg (fun mc : LiteralTranscript.Message × LiteralTranscript.Challenge => mc.2.1)
    (Option.some.inj (c.entry31.symm.trans row31))
  have bytesSame : c.queryBytes = i.queryBytes := by
    injection tags with same
    injection same
  have querySame : c.queries = q := by
    have h := c.queryDecode
    rw [bytesSame,decoded] at h
    exact (Option.some.inj h).symm
  have rawParsed := (parsedS stored tr p parsed).1
  have authenticated (k : Fin 3) := authenticated_merged H stored p rawParsed q
    merkle log Q consistent contains bound clean k.val k.isLt (frames k) (selectors k)
      (frameRead k) (rootRead k)
  have selected (k : Fin 3) (j : Fin 22) := OraclePortPackedChoiceC4.packed_agrees p q k.val
    (OraclePortAllSelectedRecoveryC6.recovered log (frames k) p k.val) (authenticated k) j.val j.isLt
  have first (j : Fin 22) : packed p q 0 (q j).val =
      OraclePortAllSelectedRecoveryC6.recovered log (frames 0) p 0 (q j).val := by
    have h := selected (0 : Fin 3) j
    change packed p q 0 (index q 0 j.val) =
      OraclePortAllSelectedRecoveryC6.recovered log (frames 0) p 0 (index q 0 j.val) at h
    simpa only [OraclePortFrozenOrderChecks.index_query,show (0:Nat) ≠ 2 by decide,ite_false] using h
  have second (j : Fin 22) : packed p q 1 (q j).val =
      OraclePortAllSelectedRecoveryC6.recovered log (frames 1) p 1 (q j).val := by
    have h := selected (1 : Fin 3) j
    change packed p q 1 (index q 1 j.val) =
      OraclePortAllSelectedRecoveryC6.recovered log (frames 1) p 1 (index q 1 j.val) at h
    simpa only [OraclePortFrozenOrderChecks.index_query,show (1:Nat) ≠ 2 by decide,ite_false] using h
  have final (j : Fin 22) : packed p q 2 (parentIndex (n := 65536) (q j)).val =
      OraclePortAllSelectedRecoveryC6.recovered log (frames 2) p 2 (parentIndex (n := 65536) (q j)).val := by
    have h := selected (2 : Fin 3) j
    change packed p q 2 (index q 2 j.val) =
      OraclePortAllSelectedRecoveryC6.recovered log (frames 2) p 2 (index q 2 j.val) at h
    simpa only [OraclePortFrozenOrderChecks.index_query,ite_true] using h
  have readerWords := OraclePortCandidateWordsC6.reader_words p q (take33 tr) i.data matching
  have init := OraclePortMapObservationsC6.initial_fibres
    (fun n => packed p q 0 n.val) (fun n => packed p q 1 n.val)
    (fun n => OraclePortAllSelectedRecoveryC6.recovered log (frames 0) p 0 n.val)
    (fun n => OraclePortAllSelectedRecoveryC6.recovered log (frames 1) p 1 n.val) q first second
  have fin := OraclePortMapObservationsC6.final_selected
    (fun n => packed p q 0 n.val) (fun n => packed p q 1 n.val)
    (fun n => packed p q 2 n.val)
    (fun n => OraclePortAllSelectedRecoveryC6.recovered log (frames 2) p 2 n.val) q final
  obtain ⟨transported⟩ := transportS tr.statement (typedRows p q tr) c
    (OraclePortFrozenOrderChecks.maps log frames p)
    (by rw [dataSame,querySame,readerWords.1]; exact init)
    (by rw [dataSame,querySame,readerWords.2]; exact fin.1)
    (by rw [dataSame,querySame,readerWords.2]; exact fin.2)
  exact toAspisChecks transported

/-! ### Admission (the property R1's clean event uses as `admitted_dV`) -/

section admission
attribute [local instance] Classical.propDecidable

/-- The 40-round admission: R1's guard on the first 33 rounds and 40 rounds.
R1's own `OraclePortAdmission.admit` requires exactly 33 rounds
(`D0ScheduleAdmission.Schedule`), so it rejects every 40-round prefix; the
Aspis clean event must use this one. -/
def admitS (core : OraclePortExperiment.Decision) : OraclePortExperiment.Decision := fun tr m =>
  if AspisR1.AspisLib.OraclePortAdmission.Guard (take33 tr) ∧ tr.rounds.length = 40 then core tr m else .done false

theorem admitted_aspis (stored : Bytes) : admitS (dV_aspis stored) = dV_aspis stored := by
  funext tr m
  unfold admitS dV_aspis
  split <;> rfl

theorem accepted_guardS (core : OraclePortExperiment.Decision) (H : Bytes → State)
    (tr : ErasedPrefix) (m : ErasedMessage) (ha : (eval H (admitS core tr m)).2 = true) :
    AspisR1.AspisLib.OraclePortAdmission.Guard (take33 tr) ∧ tr.rounds.length = 40 := by
  by_cases hg : AspisR1.AspisLib.OraclePortAdmission.Guard (take33 tr) ∧ tr.rounds.length = 40
  · exact hg
  · simp only [admitS, if_neg hg, eval, Bool.false_eq_true] at ha
end admission

#print axioms ofTypedS
#print axioms firstBatch_congr
#print axioms finalPart_ww
#print axioms transport_core
#print axioms transportS
#print axioms toAspisChecks
#print axioms typedRows_take
#print axioms accepted_checks_aspis
#print axioms admitted_aspis
#print axioms accepted_guardS
end AspisOneTx
end
