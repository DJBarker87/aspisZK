import ExtractedDigest32Begin
import ExtractedDigest32SamplerTransport

/-! Source byte and challenge provenance for the fifteen reached begin rows.
No record-byte identity or sampled-field equation is a caller premise. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1PublicPreparation.BeginProvenance
open r1_wire BeginCalls TranscriptStep

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = ok v) :
    ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

/-- Successful current accessors return the actual source array slot, including
its exact bytes. This is derived from both generated accessor bodies. -/
theorem validated_record_bytes (pre : Prefix) (row : U8) (record : ValidatedRecord)
    (h : Prefix.validated_record pre row = ok (.Ok record)) :
    record.row = row ∧ pre.records.val[row.val]? = some record.framed := by
  unfold Prefix.validated_record at h
  obtain ⟨r, hr, h⟩ := bind_success _ _ _ h
  cases r with
  | Err e =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame.from, bind_tc_ok] at h
    cases h
  | Ok framed =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at h
    have he : record = { row, framed } := (core.result.Result.Ok.inj (Result.ok.inj h)).symm
    rw [he]
    refine ⟨rfl, ?_⟩
    unfold Prefix.record at hr
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

theorem SemanticRun.row_call {H : Type} (D : aspis_core.Digest32 H) (pre : Prefix)
    {rs self after qs} (run : SemanticRun D pre rs self after qs) (row : U8)
    (hm : row ∈ rs) :
    ∃ before mid record q,
      Prefix.validated_record pre row = ok (.Ok record) ∧
      SemanticTranscript.semantic_validated D before record = ok (.Ok q, mid) ∧ q ∈ qs := by
  induction run with
  | nil => cases hm
  | @cons r rows first mid last q qs record hr hs tail ih =>
    rcases List.mem_cons.mp hm with he | hm
    · subst row
      exact ⟨first, mid, record, q, hr, hs, List.mem_cons_self ..⟩
    · obtain ⟨before, next, record, value, hr, hs, hq⟩ := ih hm
      exact ⟨before, next, record, value, hr, hs, List.mem_cons_of_mem _ hq⟩

/-- Any selected begin row uses the exact source record bytes; its first read
supplies the accepted sampler rank, and its second read supplies state carry.
The sampled value is one of this actual call's returned challenge fields. -/
theorem begin_row_provenance {H : Type} (D : aspis_core.Digest32 H)
    (pre : Prefix) (self after : SemanticTranscript H) (out : Challenges)
    (h : begin D pre self = ok (.Ok out, after)) (row : U8) (hrow : row ∈ rows) :
    ∃ (before mid : SemanticTranscript H) (record : ValidatedRecord)
      (q : aspis_core.field.QM31) (block : Bytes32) (tag next : U8) (absorbed state : Bytes32),
      record.row = row ∧ pre.records.val[row.val]? = some record.framed ∧
      record.row = before.next_row ∧ tag.val = 160 + row.val ∧ next.val = row.val + 1 ∧
      D.digest before.hash (TranscriptStep.absorbParts before.state tag record.framed) = ok absorbed ∧
      D.digest before.hash (TranscriptStep.readParts absorbed 1#u8) = ok block ∧
      D.digest before.hash (TranscriptStep.readParts absorbed 2#u8) = ok state ∧
      sampler.qm31_sample block = ok q ∧
      AspisR1.ExtractedQM31SamplerCorrect.coordinates (SamplerTransport.toOld q) =
        AspisR1.SamplerNatModel.qm31Digits (AspisR1.SourceSamplerByteRank.rank block) ∧
      mid = { before with state, next_row := next } ∧ q ∈ challengeList out := by
  obtain ⟨qs, run, hqs⟩ := begin_success D pre self after out h
  obtain ⟨before, mid, record, q, hr, hs, hq⟩ := SemanticRun.row_call D pre run row hrow
  obtain ⟨hrr, hb⟩ := validated_record_bytes pre row record hr
  obtain ⟨hnext, block, tag, next, absorbed, state, ht, hn, ha, hread, hstate, hsample, he⟩ :=
    CallerStep.semantic_step_success D before mid record q hs
  refine ⟨before, mid, record, q, block, tag, next, absorbed, state, hrr, hb,
    hnext, ?_, ?_, ha, hread, hstate, hsample,
    SamplerTransport.sample_coordinates_of_success block q hsample, he, ?_⟩
  · simpa only [hrr] using ht
  · simpa only [hrr] using hn
  · simpa only [hqs] using hq

#print axioms validated_record_bytes
#print axioms SemanticRun.row_call
#print axioms begin_row_provenance
end AspisR1PublicPreparation.BeginProvenance
