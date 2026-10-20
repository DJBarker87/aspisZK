import ExtractedDigest32Callers
import ExtractedPrefixParse
import ExtractedPrefixParserAgreement
import ExtractedPrefixTypedFull
import ExtractedRecordFraming

/-! Exact length/tag provenance from the retained Prefix parser to the retained
validated accessor. This does not identify the optimized deployed caller. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1PublicPreparation.WireTx1
open r1_wire

theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = ok v) :
    ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

def oldPrefix (pre : Prefix) : AspisR1PrefixAggregateParser.r1_wire.Prefix :=
  ⟨pre.c1_root, pre.records⟩

def Parsed (bytes : Slice U8) (pre : Prefix) : Prop :=
  AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes = ok (.Ok (oldPrefix pre))

theorem accessor_bytes (pre : Prefix) (row : U8) (record : ValidatedRecord)
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
    · simp only [lift, bind_tc_ok] at hr
      obtain ⟨actual, hi, hr⟩ := bind_success _ _ _ hr
      have ha : actual = framed := core.result.Result.Ok.inj (Result.ok.inj hr)
      unfold Array.index_usize at hi
      split at hi
      · cases hi
      · rename_i value hindex
        have hv : value = actual := Result.ok.inj hi
        change pre.records.val[(UScalar.cast .Usize row).val]? = some value at hindex
        simpa only [U8.cast_Usize_val_eq] using hindex.trans (congrArg some (hv.trans ha))

/-- Parsing, not the public Lean token structure, supplies the invariant. -/
theorem accessor_framing (bytes : Slice U8) (pre : Prefix) (hp : Parsed bytes pre)
    (row : U8) (record : ValidatedRecord)
    (ha : Prefix.validated_record pre row = ok (.Ok record)) :
    record.row = row ∧ ∃ payload,
      AspisR1.ExtractedRecordFraming.SuccessfulFraming row record.framed payload := by
  obtain ⟨hr, hs⟩ := accessor_bytes pre row record ha
  have hb : row.val < 27 := by
    obtain ⟨hh, _⟩ := List.getElem?_eq_some_iff.mp hs
    have hlen : pre.records.val.length = 27 := pre.records.property
    omega
  have hrows : AspisR1.ExtractedPrefixTrace.rowOrder[row.val]? = some row := by
    have h := congrArg (fun xs : List Nat => xs[row.val]?)
      AspisR1.ExtractedPrefixTypedFull.rowOrder_values
    rw [List.getElem?_map, List.getElem?_range hb] at h
    cases he : AspisR1.ExtractedPrefixTrace.rowOrder[row.val]? with
    | none => simp [he] at h
    | some value =>
      simp only [he, Option.map_some, Option.some.injEq] at h
      have hv : value = row := UScalar.eq_of_val_eq h
      simpa only [hv] using he
  have hm : (row, record.framed) ∈
      AspisR1.ExtractedPrefixTrace.rowOrder.zip (oldPrefix pre).records.val := by
    apply List.mem_of_getElem?
    exact List.getElem?_zip_eq_some.mpr ⟨hrows, hs⟩
  obtain ⟨payload, hparse⟩ := AspisR1.ExtractedPrefixParse.parse_record_of_success
    bytes (oldPrefix pre) hp row record.framed hm
  exact ⟨hr, payload, AspisR1.ExtractedRecordFraming.parse_record_success _ _ _
    (AspisR1.ExtractedPrefixParserAgreement.parse_record_success _ _ _ hparse)⟩

#print axioms bind_success
#print axioms accessor_bytes
#print axioms accessor_framing
end AspisR1PublicPreparation.WireTx1
