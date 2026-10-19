import ExtractedRecordByteCanonicality
import ExtractedRecordHighZero

/-!
Successful-return facts for the actual record-field validator. The theorem
covers remaining complete chunks and makes no assertion about the remainder.
-/
set_option autoImplicit false

namespace AspisR1.ExtractedRecordValidator
open Aeneas Aeneas.Std Result ControlFlow
open AspisR1RecordParser
open field.wide_exact
open ExtractedRecordByteCanonicality ExtractedRecordLimbCanonicality
open ExtractedRecordHighZero

abbrev Iter := core.iter.adapters.enumerate.Enumerate (core.slice.iter.ChunksExact U8)
abbrev Status := core.result.Result Unit r1_wire.Error

def ChunkValid (chunk : Slice U8) : Prop :=
  ∃ w, WideExact.from_le_bytes chunk = ok (some w) ∧ w.c1 = field.QM31.ZERO

theorem loop_unroll (iter : Iter) (row : U8) :
    r1_wire.validate_record_fields_loop iter row = (do
      let r ← r1_wire.validate_record_fields_loop.body row iter
      match r with
      | cont next => r1_wire.validate_record_fields_loop next row
      | done result => ok result) := by
  conv_lhs => unfold r1_wire.validate_record_fields_loop; rw [loop]
  cases hb : r1_wire.validate_record_fields_loop.body row iter with
  | fail e => simp only [bind_tc_fail]
  | div => simp only [bind_tc_div]
  | ok r =>
    cases r with
    | done result => simp only [bind_tc_ok]
    | cont next =>
      simp only [bind_tc_ok]
      rfl

private theorem enumerate_cons (iter : Iter) (chunk : Slice U8)
    (chunks : List (Slice U8)) (hc : iter.iter.chunks = chunk :: chunks) :
    core.iter.adapters.enumerate.IteratorEnumerate.next
      (core.iter.traits.iterator.IteratorChunksExact U8) iter = (do
        let count' ← iter.count + 1#usize
        ok (some (iter.count, chunk),
          ({ iter := { chunks := chunks, remainder := iter.iter.remainder }, count := count' } :
            Iter))) := by
  simp only [core.iter.adapters.enumerate.IteratorEnumerate.next,
    core.slice.iter.IteratorChunksExact.next, hc, bind_tc_ok]

/-- Success validates every remaining chunk, for arbitrary counter/remainder.
No counter bound is assumed: an overflowing increment cannot return success. -/
theorem loop_success (iter : Iter) (row : U8)
    (h : r1_wire.validate_record_fields_loop iter row = ok (core.result.Result.Ok ())) :
    ∀ chunk ∈ iter.iter.chunks, ChunkValid chunk := by
  rw [loop_unroll] at h
  cases hc : iter.iter.chunks with
  | nil => simp
  | cons chunk chunks =>
    have he := enumerate_cons iter chunk chunks hc
    cases ha : iter.count + 1#usize with
    | fail e =>
      simp only [ha, bind_tc_fail] at he
      simp only [r1_wire.validate_record_fields_loop.body, he, bind_tc_fail] at h
      cases h
    | div =>
      simp only [ha, bind_tc_div] at he
      simp only [r1_wire.validate_record_fields_loop.body, he, bind_tc_div] at h
      cases h
    | ok count' =>
      let next : Iter :=
        { iter := { chunks := chunks, remainder := iter.iter.remainder }, count := count' }
      have hn : core.iter.adapters.enumerate.IteratorEnumerate.next
          (core.iter.traits.iterator.IteratorChunksExact U8) iter =
          ok (some (iter.count, chunk), next) := by
        simpa only [ha, bind_tc_ok] using he
      simp only [r1_wire.validate_record_fields_loop.body, hn, bind_tc_ok] at h
      cases hd : WideExact.from_le_bytes chunk with
      | fail e =>
        cases h
      | div =>
        cases h
      | ok decoded =>
        cases decoded with
        | none =>
          simp [hd, AspisR1RecordParser.core.option.Option.ok_or,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at h
        | some w =>
          simp only [bind_tc_ok, AspisR1RecordParser.core.option.Option.ok_or,
            core.result.Result.Insts.CoreOpsTry.branch, WideExact.impl.c1] at h
          cases hz : core.cmp.PartialEq.ne.trait_default
              field.QM31.Insts.CoreCmpPartialEqQM31 w.c1 field.QM31.ZERO with
          | fail e =>
            cases h
          | div =>
            cases h
          | ok bad =>
            cases bad with
            | true =>
              cases h
            | false =>
              change r1_wire.validate_record_fields_loop next row =
                ok (core.result.Result.Ok ()) at h
              have ih := loop_success next row h
              have hzero : w.c1 = field.QM31.ZERO := (qm31_ne_false_iff _ _).mp hz
              intro candidate hmem
              rcases List.mem_cons.mp hmem with rfl | hmem
              · exact ⟨w, hd, hzero⟩
              · exact ih candidate hmem
termination_by iter.iter.chunks.length
decreasing_by simp only [next, hc, List.length_cons]; omega

end AspisR1.ExtractedRecordValidator

#print axioms AspisR1.ExtractedRecordValidator.loop_unroll
#print axioms AspisR1.ExtractedRecordValidator.loop_success
