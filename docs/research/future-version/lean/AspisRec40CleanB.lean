import RWireCheckedFormat
import AspisRows40Literal
import AspisRec40CleanStatement

/-! Aspis 40-row clean event, part 2: constructor schedule, row validity and
`RWireCheckedFormat.Format` from the fields of `AspisChecks` (copies of
`RawChecksConstructorSchedule.checks_force_constructor_schedule` and
`RWireCheckedFormat.format_of_checks`, reading only `data`, `matchingRead`
and the row-31/32 entries on the first 33 rounds). -/
set_option autoImplicit false
noncomputable section
namespace AspisRec40.CleanB
open FS FS2 FS2.Duplex R0C.V3
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8PairedCommitment
open AspisR1 OraclePortStoredExperimentC4 OraclePortStoredAdmissionC4
open RawCutProverCompiler (experiment)
open CanonicalCutEnrichedTranscript (Words enrichMessage)

abbrev pr (D : LiteralByteProtocol.Decoder) := AspisRows40.Protocol.protocol D

/-! ## Schedule and format from `AspisChecks` -/

private theorem rowEntry_of_valid_getElem
    (rs : List (LiteralTranscript.Message × LiteralTranscript.Challenge))
    (i : Nat) (hi : i < rs.length)
    (hv : LiteralTranscript.valid i (rs[i]'hi).1) :
    ∃ m c, rs[i]? = some (m, c) ∧ LiteralTranscript.valid i m :=
  ⟨(rs[i]'hi).1, (rs[i]'hi).2, List.getElem?_eq_getElem hi, hv⟩

private theorem valid_of_readAt
    (rs : List (LiteralTranscript.Message × LiteralTranscript.Challenge))
    (i : Nat) (hi : i < rs.length) {A : Type}
    (decode : AspisV8R19.DuplexFrames.Bytes → Option A) (value : A)
    (h : LiteralOpeningStages.readAt rs i decode = some value) :
    LiteralTranscript.valid i (rs[i]'hi).1 :=
  LiteralIndexedPrefix.readAt_success_index_valid rs i hi decode value h

/-- Copy of `RawChecksConstructorSchedule.checks_force_constructor_schedule`
with the two fields it reads (`data`, `matchingRead`) as arguments. -/
theorem schedule_of_matching
    (rs : List (LiteralTranscript.Message × LiteralTranscript.Challenge))
    (data : MatchingSupport.Data AspisAcceptance.EW)
    (matchingRead : LiteralMatchingData.read rs = some data)
    (hlen : 32 ≤ rs.length) :
    ∀ i, i ≤ 30 → ∃ m c, rs[i]? = some (m, c) ∧ LiteralTranscript.valid i m := by
  obtain ⟨common, staged, row31, word, gamma, kappa, alpha0, alpha1,
    hcommon, hstaged, hrow31, hword, hgamma, hkappa, halpha0, halpha1, _⟩ :=
      LiteralMatchingFacts.read_success_components rs data matchingRead
  obtain ⟨hprefixLen, _hc1, _hc2, hsemantic, _hword⟩ :=
    LiteralOpeningPrefixFacts.read_prefix_components rs common hcommon
  have hsplit : rs.take 25 ++ rs.drop 25 = rs := List.take_append_drop 25 rs
  have hgammaRows := LiteralReadAtFacts.readGamma_current rs staged.toFirst.toKappa.toGamma
    (LiteralStageFacts.readSecond_gamma rs staged hstaged)
  have hkappaRow := LiteralReadAtFacts.readKappa_current rs staged.toFirst.toKappa
    (LiteralStageFacts.readSecond_kappa rs staged hstaged)
  have hfirstRow := LiteralReadAtFacts.readFirst_current rs staged.toFirst
    (LiteralStageFacts.readSecond_first rs staged hstaged)
  have hsecondRow := LiteralReadAtFacts.readSecond_current rs staged hstaged
  intro i hi
  by_cases hsmall : i < 25
  · have hsmallIndex : i < (rs.take 25).length := by
      rw [hprefixLen]
      exact hsmall
    obtain ⟨hrow, parsed, challenge, hparse, _hchallenge, _houtput⟩ :=
      LiteralSemanticIndex.read_index LiteralOpeningView.eK 0 (rs.take 25)
        common.semantic hsemantic i hsmallIndex
    have hparse' := by simpa only [Nat.zero_add] using hparse
    have hv := LiteralSemanticNoHit.parseMessage_valid LiteralOpeningView.eK
      ⟨i, by omega⟩ ((rs.take 25)[i]'hsmallIndex).1 parsed hparse'
    have htakeToFull : (rs.take 25)[i]? = rs[i]? := by
      have happ := List.getElem?_append_left (l₂ := rs.drop 25) hsmallIndex
      rw [hsplit] at happ
      exact happ.symm
    obtain ⟨m, c, hget, hv'⟩ :=
      rowEntry_of_valid_getElem (rs.take 25) i hsmallIndex hv
    exact ⟨m, c, htakeToFull.symm.trans hget, hv'⟩
  · have hi : i < rs.length := by omega
    have he := rowEntry_of_valid_getElem rs i hi
    have h25 := valid_of_readAt rs 25 (by omega)
      (AspisR1.CircleRecordCodec.decode 0) staged.toFirst.toKappa.toGamma.row25 hgammaRows.1
    have h26 := valid_of_readAt rs 26 (by omega)
      (AspisR1.CircleRecordCodec.decode 1) staged.toFirst.toKappa.toGamma.row26 hgammaRows.2.1
    have h27 := valid_of_readAt rs 27 (by omega)
      (AspisR1.OpeningRecordCodec.decode .gamma) staged.toFirst.toKappa.toGamma.row27 hgammaRows.2.2
    have h28 := valid_of_readAt rs 28 (by omega)
      (AspisR1.OpeningRecordCodec.decode .kappa) staged.toFirst.toKappa.row28 hkappaRow
    have h29 := valid_of_readAt rs 29 (by omega)
      (AspisR1.OpeningRecordCodec.decode .first) staged.toFirst.row29 hfirstRow
    have h30 := valid_of_readAt rs 30 (by omega)
      (AspisR1.OpeningRecordCodec.decode .second) staged.row30 hsecondRow
    have hrows : i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 := by omega
    rcases hrows with hi25 | hi26 | hi27 | hi28 | hi29 | hi30
    · subst i; exact he h25
    · subst i; exact he h26
    · subst i; exact he h27
    · subst i; exact he h28
    · subst i; exact he h29
    · subst i; exact he h30

theorem take33_eq (D : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (pub : LiteralTranscript.Public) (pf : LiteralProtocol.Proof) :
    ((pr D).transcript H pub pf 40).rounds.take 33 =
      ((LiteralByteProtocol.protocol D).transcript H pub pf 33).rounds :=
  (AspisRows40.Literal.transcript_take33 D _ H pub pf 40 (by omega)).2

/-- Validity of rows 0 to 32 of the proof, from `AspisChecks` on its 40-row transcript. -/
theorem valid_of_checks (D : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (pub : LiteralTranscript.Public) (pf : LiteralProtocol.Proof)
    (c : AspisAcceptance.AspisChecks AspisOneTx.decodePairS pub
      ((pr D).transcript H pub pf 40).rounds) :
    ∀ i < 33, LiteralTranscript.valid i (pf i) := by
  let rs := ((LiteralByteProtocol.protocol D).transcript H pub pf 33).rounds
  have hindex (i : Nat) (hi : i < 33) :=
    LiteralByteRunFacts.transcript_index D H pub pf 33 i hi
  have hlen : rs.length = 33 := LiteralByteRunFacts.transcript_round D H pub pf 33
  have hmr : LiteralMatchingData.read rs = some c.data := by
    have h := c.matchingRead
    rw [take33_eq] at h
    exact h
  have hv := schedule_of_matching rs c.data hmr (by omega)
  have valid_of_entry (i : Nat) (m : LiteralTranscript.Message) (ch : LiteralTranscript.Challenge)
      (hi : i < 33) (he : rs[i]? = some (m,ch)) (h : LiteralTranscript.valid i m) :
      LiteralTranscript.valid i (pf i) := by
    have hm : m = pf i := congrArg Prod.fst (Option.some.inj (he.symm.trans (hindex i hi)))
    rw [← hm]
    exact h
  intro i hi
  by_cases h30 : i ≤ 30
  · obtain ⟨m,ch,he,h⟩ := hv i h30
    exact valid_of_entry i m ch hi he h
  · have hcases : i = 31 ∨ i = 32 := by omega
    have e31 : rs[31]? = some (c.m31, (TranscriptView.Value.queries (.ok c.queryBytes), c.state31)) := by
      have h := c.entry31
      rw [take33_eq] at h
      exact h
    have e32 : rs[32]? = some (c.m32, (TranscriptView.Value.ordinary c.rho, c.state32)) := by
      have h := c.entry32
      rw [take33_eq] at h
      exact h
    rcases hcases with rfl | rfl
    · exact valid_of_entry 31 c.m31 _ (by decide) e31 c.valid31
    · exact valid_of_entry 32 c.m32 _ (by decide) e32 c.valid32

/-- Copy of `RWireCheckedFormat.format_of_checks`, from `AspisChecks` fields. -/
theorem format_of_checks (D : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (pub : LiteralTranscript.Public) (pf : LiteralProtocol.Proof)
    (c : AspisAcceptance.AspisChecks AspisOneTx.decodePairS pub
      ((pr D).transcript H pub pf 40).rounds) : RWireCheckedFormat.Format pf := by
  let rs := ((LiteralByteProtocol.protocol D).transcript H pub pf 33).rounds
  have hindex (i : Nat) (hi : i < 33) :=
    LiteralByteRunFacts.transcript_index D H pub pf 33 i hi
  have hmr : LiteralMatchingData.read rs = some c.data := by
    have h := c.matchingRead
    rw [take33_eq] at h
    exact h
  have hvalid := valid_of_checks D H pub pf c
  refine ⟨hvalid, ?_⟩
  obtain ⟨common, staged, row31, word, gamma, kappa, alpha0, alpha1,
    hcommon, hstaged, hrow31, hword, hgamma, hkappa, halpha0, halpha1, _⟩ :=
    LiteralMatchingFacts.read_success_components rs c.data hmr
  obtain ⟨hprelen, _, _, hsemantic, _⟩ :=
    LiteralOpeningPrefixFacts.read_prefix_components rs common hcommon
  obtain ⟨hr, parsed, ch, hp, _, _⟩ :=
    LiteralSemanticIndex.read_index LiteralOpeningView.eK 0 (rs.take 25)
      common.semantic hsemantic 2 (by omega)
  have hget2 : (rs.take 25)[2]'(by omega) = (pf 2,
      (eval H (LiteralByteSampler.samp 2
        ((LiteralByteProtocol.protocol D).transcript H pub pf 2) (pf 2)).toProgram).2) := by
    apply Option.some.inj
    rw [← List.getElem?_eq_getElem]
    simpa using hindex 2 (by decide)
  rw [hget2] at hp
  have hp30 := LiteralReadAtFacts.readSecond_current rs staged hstaged
  unfold LiteralOpeningStages.readAt at hp30
  rw [hindex 30 (by decide)] at hp30
  simp only [Option.bind_some, if_pos (hvalid 30 (by decide))] at hp30
  cases h0 : pf 0 <;> try { have := hvalid 0 (by decide); simp [h0, LiteralTranscript.valid] at this }
  rename_i r1 w1
  cases h2 : pf 2 <;> try { have := hvalid 2 (by decide); simp [h2, LiteralTranscript.valid] at this }
  rename_i b2 w2
  cases h30 : pf 30 <;> try { have := hvalid 30 (by decide); simp [h30, LiteralTranscript.valid] at this }
  rename_i b30 w30
  rw [h2] at hp
  have hv2 : LiteralTranscript.valid 2 (.c2 b2 w2) := by
    simpa only [h2] using hvalid 2 (by decide)
  unfold LiteralSemanticPrefix.parseMessage at hp
  rw [if_pos hv2] at hp
  change (SemanticRecordCodec.decode ⟨2, by decide⟩ b2.val).map _ = some parsed at hp
  cases hd : SemanticRecordCodec.decode ⟨2, by decide⟩ b2.val with
  | none => rw [hd] at hp; cases hp
  | some payload =>
    obtain ⟨value, hvrow⟩ := payload
    cases value with
    | empty => simp [SemanticRecordCodec.validRow] at hvrow
    | maskSum value => simp [SemanticRecordCodec.validRow] at hvrow
    | polynomial value => simp [SemanticRecordCodec.validRow] at hvrow
    | c2Root r2 =>
      refine ⟨r1, w1, b2, w2, r2, b30, w30, staged.row30, rfl, rfl, rfl, hd, ?_⟩
      simpa [h30, LiteralTranscript.erase] using hp30

#print axioms schedule_of_matching
#print axioms valid_of_checks
#print axioms format_of_checks

end AspisRec40.CleanB
end
