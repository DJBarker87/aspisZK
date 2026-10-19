import RawActualAnnotatedChallengeSequence
import ExtractedPrefixTypedFullCurrent
import R1SemanticPayloadView
import RawActualPolynomialRowAgreement
import R1SemanticPrefixCodec

set_option autoImplicit false
noncomputable section
namespace AspisR1PublicPreparation.RawActualAnnotatedTypedRows

open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.RawActualAnnotatedChallengeSequence

abbrev Outcome := AspisR1PublicPreparation.SemanticRoundsCheckedTrace.Outcome

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = ok v) : ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

/-- Source-shaped slot readback for the current generated Prefix owner. -/
theorem validated_record_bytes (pre : AspisR1PublicPreparation.r1_wire.Prefix)
    (row : U8) (record : AspisR1PublicPreparation.r1_wire.ValidatedRecord)
    (h : AspisR1PublicPreparation.r1_wire.Prefix.validated_record pre row =
      ok (.Ok record)) :
    record.row = row ∧ pre.records.val[row.val]? = some record.framed := by
  unfold AspisR1PublicPreparation.r1_wire.Prefix.validated_record at h
  obtain ⟨r, hr, h⟩ := bind_success _ _ _ h
  cases r with
  | Err e =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame.from, bind_tc_ok] at h
    cases h
  | Ok framed =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at h
    have he : record = { row, framed } :=
      (core.result.Result.Ok.inj (Result.ok.inj h)).symm
    rw [he]
    refine ⟨rfl, ?_⟩
    unfold AspisR1PublicPreparation.r1_wire.Prefix.record at hr
    split at hr
    · cases hr
    · rename_i hrow
      simp only [lift, bind_tc_ok] at hr
      obtain ⟨actual, hi, hr⟩ := bind_success _ _ _ hr
      have ha : actual = framed := core.result.Result.Ok.inj (Result.ok.inj hr)
      unfold Array.index_usize at hi
      split at hi
      · cases hi
      · rename_i value hindex
        have hv : value = actual := Result.ok.inj hi
        change pre.records.val[(UScalar.cast .Usize row).val]? = some value at hindex
        simpa only [U8.cast_Usize_val_eq] using hindex.trans (congrArg some (hv.trans ha))

/-- An annotated list preserves the event pairs position by position. -/
theorem annotated_events {H : Type}
    {D : AspisR1PublicPreparation.aspis_core.Digest32 H}
    {pre : AspisR1PublicPreparation.r1_wire.Prefix}
    {events : List (Usize × U8)} {initial final : Outcome H}
    {entries : List (RoundEvidence D pre)}
    (hrun : AnnotatedRun D pre events initial final entries) :
    entries.map (fun entry => (entry.round, entry.row)) = events := by
  induction hrun with
  | nil => rfl
  | @cons entry events final entries tail ih =>
      simpa only [List.map_cons] using
        congrArg (List.cons (entry.round, entry.row)) ih

/-- The actual fixed schedule associates each round with semantic row 15+round. -/
theorem entry_schedule_row {H : Type}
    {D : AspisR1PublicPreparation.aspis_core.Digest32 H}
    {pre : AspisR1PublicPreparation.r1_wire.Prefix}
    {initial final : Outcome H} {entries : List (RoundEvidence D pre)}
    (hrun : AnnotatedRun D pre
      AspisR1PublicPreparation.SemanticRoundsCheckedTrace.schedule initial final entries)
    (entry : RoundEvidence D pre) (hentry : entry ∈ entries) :
    entry.row.val = 15 + entry.round.val := by
  have hmap := annotated_events hrun
  have hmem : (entry.round, entry.row) ∈
      AspisR1PublicPreparation.SemanticRoundsCheckedTrace.schedule := by
    rw [← hmap]
    exact List.mem_map.mpr ⟨entry, hentry, rfl⟩
  have hcases :
      (entry.round.val = 0 ∧ entry.row.val = 15) ∨
      (entry.round.val = 1 ∧ entry.row.val = 16) ∨
      (entry.round.val = 2 ∧ entry.row.val = 17) ∨
      (entry.round.val = 3 ∧ entry.row.val = 18) ∨
      (entry.round.val = 4 ∧ entry.row.val = 19) ∨
      (entry.round.val = 5 ∧ entry.row.val = 20) ∨
      (entry.round.val = 6 ∧ entry.row.val = 21) ∨
      (entry.round.val = 7 ∧ entry.row.val = 22) ∨
      (entry.round.val = 8 ∧ entry.row.val = 23) ∨
      (entry.round.val = 9 ∧ entry.row.val = 24) := by
    simpa [AspisR1PublicPreparation.SemanticRoundsCheckedTrace.schedule,
      Prod.mk.injEq] using hmem
  rcases hcases with h | h | h | h | h | h | h | h | h | h <;> omega

/-- Actual parsed full-prefix values decode the very framed record retained by
an annotated round, at that round's typed semantic row. -/
theorem annotated_entry_decodes_parsed_row {H : Type}
    (bytes : Slice U8)
    (pre : AspisR1PublicPreparation.r1_wire.Prefix)
    (hparse : AspisR1PublicPreparation.PrefixAdapter.parseAccepted bytes =
      .ok (.Ok pre))
    (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (initial final : Outcome H)
    (entries : List (RoundEvidence D pre))
    (hrun : AnnotatedRun D pre
      AspisR1PublicPreparation.SemanticRoundsCheckedTrace.schedule initial final entries)
    (entry : RoundEvidence D pre) (hentry : entry ∈ entries) :
    ∃ values : AspisR1.SemanticPrefixCodec.Full,
      AspisR1.SemanticPrefixCodec.encodeFull values =
        AspisR1PublicPreparation.PrefixAdapter.completedRecords pre ∧
      AspisR1.SemanticRecordCodec.decode
        ⟨15 + entry.round.val, by
          have hrow := entry_schedule_row hrun entry hentry
          have hr := entry.round.val
          have hs : (entry.round, entry.row) ∈
              AspisR1PublicPreparation.SemanticRoundsCheckedTrace.schedule := by
            rw [← annotated_events hrun]
            exact List.mem_map.mpr ⟨entry, hentry, rfl⟩
          have hlt : entry.round.val < 10 := by
            simp [AspisR1PublicPreparation.SemanticRoundsCheckedTrace.schedule,
              Prod.mk.injEq] at hs
            omega
          omega⟩
        (entry.record.framed.val.map AspisR1.ExtractedRecordByteValue.rawByte) =
      some (values ⟨15 + entry.round.val, by
        have hs : (entry.round, entry.row) ∈
            AspisR1PublicPreparation.SemanticRoundsCheckedTrace.schedule := by
          rw [← annotated_events hrun]
          exact List.mem_map.mpr ⟨entry, hentry, rfl⟩
        have hlt : entry.round.val < 10 := by
          simp [AspisR1PublicPreparation.SemanticRoundsCheckedTrace.schedule,
            Prod.mk.injEq] at hs
          omega
        omega⟩) := by
  obtain ⟨values, _hdecode, hfull, _hentries⟩ :=
    AspisR1PublicPreparation.PrefixAdapter.parse_typedFull bytes pre hparse
  refine ⟨values, hfull, ?_⟩
  let i : Nat := 15 + entry.round.val
  have hround : entry.row.val = i := entry_schedule_row hrun entry hentry
  have hi25 : i < 25 := by
    have hs : (entry.round, entry.row) ∈
        AspisR1PublicPreparation.SemanticRoundsCheckedTrace.schedule := by
      rw [← annotated_events hrun]
      exact List.mem_map.mpr ⟨entry, hentry, rfl⟩
    have hr : entry.round.val < 10 := by
      simp [AspisR1PublicPreparation.SemanticRoundsCheckedTrace.schedule,
        Prod.mk.injEq] at hs
      omega
    dsimp [i]
    omega
  have hslot := validated_record_bytes
    pre entry.row entry.record entry.recordOk
  have hraw : pre.records.val[i]? = some entry.record.framed := by
    simpa [hround, i] using hslot.2
  have hcompleted :
      AspisR1PublicPreparation.PrefixAdapter.completedRecords pre[i]? =
        some (entry.record.framed.val.map AspisR1.ExtractedRecordByteValue.rawByte) := by
    unfold AspisR1PublicPreparation.PrefixAdapter.completedRecords
    rw [List.getElem?_map]
    rw [List.getElem?_take_of_lt (l := pre.records.val) (i := i) (j := 25) hi25]
    simpa using congrArg (Option.map
      (fun frame => frame.val.map AspisR1.ExtractedRecordByteValue.rawByte)) hraw
  have hencoded :
      AspisR1.SemanticPrefixCodec.encodeFull values[i]? =
        some (AspisR1.SemanticRecordCodec.encode
          (values ⟨i, hi25⟩).val) := by
    simp only [AspisR1.SemanticPrefixCodec.encodeFull, List.getElem?_map]
    rw [List.getElem?_eq_getElem (by
      simp only [AspisR1.SemanticPrefixCodec.entriesOf_length]
      exact hi25)]
    simp only [AspisR1.SemanticPrefixCodec.entriesOf_getElem,
      AspisR1.SemanticPrefixCodec.encodeEntry]
    rfl
  have hget := congrArg (fun xs : List AspisR1.SemanticRecordCodec.Bytes => xs[i]?) hfull
  rw [hencoded, hcompleted] at hget
  have hframe : AspisR1.SemanticRecordCodec.encode (values ⟨i, hi25⟩).val =
      entry.record.framed.val.map AspisR1.ExtractedRecordByteValue.rawByte :=
    Option.some.inj hget
  rw [← hframe]
  exact AspisR1.SemanticRecordCodec.decode_encode ⟨i, hi25⟩ (values ⟨i, hi25⟩).val


/-- The same actual record at its scheduled semantic row supplies the typed
coefficient polynomial used by the canonical semantic view. -/
theorem annotated_entry_polynomial_agrees {H : Type}
    (bytes : Slice U8)
    (pre : AspisR1PublicPreparation.r1_wire.Prefix)
    (hparse : AspisR1PublicPreparation.PrefixAdapter.parseAccepted bytes =
      .ok (.Ok pre))
    (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (initial final : Outcome H)
    (entries : List (RoundEvidence D pre))
    (hrun : AnnotatedRun D pre
      AspisR1PublicPreparation.SemanticRoundsCheckedTrace.schedule initial final entries)
    (entry : RoundEvidence D pre) (hentry : entry ∈ entries) :
    ∃ values : AspisR1.SemanticPrefixCodec.Full,
      AspisR1.SemanticRecordCodec.decode
        ⟨15 + entry.round.val, by
          have hs : (entry.round, entry.row) ∈
              AspisR1PublicPreparation.SemanticRoundsCheckedTrace.schedule := by
            rw [← annotated_events hrun]
            exact List.mem_map.mpr ⟨entry, hentry, rfl⟩
          have hlt : entry.round.val < 10 := by
            simp [AspisR1PublicPreparation.SemanticRoundsCheckedTrace.schedule,
              Prod.mk.injEq] at hs
            omega
          omega⟩
        (entry.record.framed.val.map AspisR1.ExtractedRecordByteValue.rawByte) =
      some (values ⟨15 + entry.round.val, by
        have hs : (entry.round, entry.row) ∈
            AspisR1PublicPreparation.SemanticRoundsCheckedTrace.schedule := by
          rw [← annotated_events hrun]
          exact List.mem_map.mpr ⟨entry, hentry, rfl⟩
        have hlt : entry.round.val < 10 := by
          simp [AspisR1PublicPreparation.SemanticRoundsCheckedTrace.schedule,
            Prod.mk.injEq] at hs
          omega
        omega⟩) ∧
      (AspisR1PublicPreparation.RawSemanticCheckedStepPolynomialAdapter.exactPolynomial
          entry.coefficients).map
        (algebraMap AspisR1.ExtractedMaskQM31Exact.QM31Exact AspisWideTower.WideExact) =
        AspisR1.SemanticCoefficientCodec.polynomial
          (AspisR1.SemanticPayloadView.coeffAt values entry.round) := by
  obtain ⟨values, _hfull, htyped⟩ := annotated_entry_decodes_parsed_row
    bytes pre hparse D initial final entries hrun entry hentry
  have hi : 15 + entry.round.val < 25 := by
    have hs : (entry.round, entry.row) ∈
        AspisR1PublicPreparation.SemanticRoundsCheckedTrace.schedule := by
      rw [← annotated_events hrun]
      exact List.mem_map.mpr ⟨entry, hentry, rfl⟩
    have hlt : entry.round.val < 10 := by
      simp [AspisR1PublicPreparation.SemanticRoundsCheckedTrace.schedule,
        Prod.mk.injEq] at hs
      omega
    omega
  have hpoly := AspisR1.SemanticPayloadView.coeffAt_payload values entry.round
  have hactual := AspisR1PublicPreparation.RawActualPolynomialRowAgreement.actual_polynomial_row_agrees
    ⟨15 + entry.round.val, hi⟩ entry.record entry.coefficients
    (values ⟨15 + entry.round.val, hi⟩)
    (AspisR1.SemanticPayloadView.coeffAt values entry.round) hpoly entry.decodeOk htyped
  exact ⟨values, htyped, hactual⟩

#print axioms annotated_entry_polynomial_agrees
#print axioms annotated_events
#print axioms entry_schedule_row
#print axioms annotated_entry_decodes_parsed_row
end AspisR1PublicPreparation.RawActualAnnotatedTypedRows
end
