import RPz7_ExtractedDigest32Begin
/-! An ordered log constructed from the actual semantic call witnesses.
This generic source lemma does not assume record-byte equality. Applying it
to verifier acceptance still requires the actual remaining-row reachability. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1PublicPreparation.SourceFull25
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

structure Call {H : Type} (D : aspis_core.Digest32 H) (pre : Prefix) where
  row : U8
  before : SemanticTranscript H
  after : SemanticTranscript H
  record : ValidatedRecord
  q : aspis_core.field.QM31
  tag : U8
  next : U8
  absorbed : Bytes32
  block : Bytes32
  state : Bytes32
  validated : Prefix.validated_record pre row = ok (.Ok record)
  semantic : SemanticTranscript.semantic_validated D before record = ok (.Ok q, after)
  record_row : record.row = row
  slot : pre.records.val[row.val]? = some record.framed
  before_row : record.row = before.next_row
  tag_code : tag.val = 160 + record.row.val
  next_row : next.val = record.row.val + 1
  absorb : D.digest before.hash (absorbParts before.state tag record.framed) = ok absorbed
  read1 : D.digest before.hash (readParts absorbed 1#u8) = ok block
  read2 : D.digest before.hash (readParts absorbed 2#u8) = ok state
  sample : sampler.qm31_sample block = ok q
  carried : after = { before with state, next_row := next }

inductive Trace {H : Type} (D : aspis_core.Digest32 H) (pre : Prefix) :
    SemanticTranscript H → SemanticTranscript H → List (Call D pre) → Prop
  | nil (self) : Trace D pre self self []
  | cons {after cs} (c : Call D pre) (tail : Trace D pre c.after after cs) :
      Trace D pre c.before after (c :: cs)

/-- Every stored log cell comes from the same validated-record access and the
same three actual Digest32 calls, with the actual q and carried successor. -/
theorem calls_of_run {H : Type} (D : aspis_core.Digest32 H) (pre : Prefix)
    {rows before after qs} (run : SemanticRun D pre rows before after qs) :
    ∃ cs : List (Call D pre), Trace D pre before after cs ∧
      cs.map Call.row = rows ∧ cs.map Call.q = qs := by
  induction run with
  | nil self => exact ⟨[], .nil self, rfl, rfl⟩
  | @cons row rows before mid after q qs record hr hs tail ih =>
    obtain ⟨cs, ht, hrows, hqs⟩ := ih
    obtain ⟨hrr, hslot⟩ := validated_record_bytes pre row record hr
    obtain ⟨hbefore, block, tag, next, absorbed, state, htag, hnext, ha, h1, h2, hq, he⟩ :=
      CallerStep.semantic_step_success D before mid record q hs
    let c : Call D pre := ⟨row, before, mid, record, q, tag, next, absorbed, block, state,
      hr, hs, hrr, hslot, hbefore, htag, hnext, ha, h1, h2, hq, he⟩
    exact ⟨c :: cs, .cons c ht,
      by simpa only [List.map_cons, c] using congrArg (List.cons row) hrows,
      by simpa only [List.map_cons, c] using congrArg (List.cons q) hqs⟩

theorem frames_eq_slots {H : Type} (D : aspis_core.Digest32 H) (pre : Prefix)
    (cs : List (Call D pre)) :
    cs.map (fun c => c.record.framed) =
      (cs.map Call.row).filterMap (fun row => pre.records.val[row.val]?) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.map_cons, List.filterMap_cons, c.slot, ih]

private theorem range_slots_take {α : Type} (xs : List α) (n : Nat) :
    (List.range n).filterMap (fun i => xs[i]?) = xs.take n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.filterMap_append, ih, List.take_add_one]
    cases hs : xs[n]? <;> simp only [List.filterMap_cons, List.filterMap_nil, hs] <;> rfl

/-- The ordered source frames equal the same parsed array's first25 entries.
There is no hbytes premise, selected record list, or independent state witness. -/
theorem run_full25_frames {H : Type} (D : aspis_core.Digest32 H) (pre : Prefix)
    {rows before after qs} (run : SemanticRun D pre rows before after qs)
    (hrows : rows.map (fun row => row.val) = List.range 25) :
    ∃ cs : List (Call D pre), Trace D pre before after cs ∧
      cs.map Call.row = rows ∧ cs.map Call.q = qs ∧
      cs.map (fun c => c.record.framed) = pre.records.val.take 25 := by
  obtain ⟨cs, ht, hr, hq⟩ := calls_of_run D pre run
  refine ⟨cs, ht, hr, hq, ?_⟩
  rw [frames_eq_slots, hr]
  have hf := congrArg (List.filterMap (fun i => pre.records.val[i]?)) hrows
  simpa only [List.filterMap_map, Function.comp_apply] using
    hf.trans (range_slots_take pre.records.val 25)

#print axioms validated_record_bytes
#print axioms calls_of_run
#print axioms frames_eq_slots
#print axioms run_full25_frames
end AspisR1PublicPreparation.SourceFull25
