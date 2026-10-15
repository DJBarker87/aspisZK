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
      change (do
        let result ← (do
          let decoded ← WideExact.from_le_bytes chunk
          let status ← AspisR1RecordParser.core.option.Option.ok_or decoded
            (r1_wire.Error.NonCanonical row iter.count)
          let branch ← core.result.Result.Insts.CoreOpsTry.branch status
          match branch with
          | core.ops.control_flow.ControlFlow.Continue w => do
            let q ← WideExact.impl.c1 w
            let bad ← core.cmp.PartialEq.ne.trait_default
              field.QM31.Insts.CoreCmpPartialEqQM31 q field.QM31.ZERO
            if bad then ok (done (core.result.Result.Err
              (r1_wire.Error.NonCanonical row iter.count)))
            else ok (cont next)
          | core.ops.control_flow.ControlFlow.Break residual => do
            let result ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              Unit (core.convert.FromSame r1_wire.Error) residual
            ok (done result) : Result (ControlFlow Iter Status))
        match result with
        | cont next => r1_wire.validate_record_fields_loop next row
        | done result => ok result) = ok (core.result.Result.Ok ()) at h
      cases hd : WideExact.from_le_bytes chunk with
      | fail e =>
        simp only [hd, bind_tc_fail] at h
        cases h
      | div =>
        simp only [hd, bind_tc_div] at h
        cases h
      | ok decoded =>
        cases decoded with
        | none =>
          simp [hd, AspisR1RecordParser.core.option.Option.ok_or,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at h
        | some w =>
          simp only [hd, bind_tc_ok, AspisR1RecordParser.core.option.Option.ok_or,
            core.result.Result.Insts.CoreOpsTry.branch, WideExact.impl.c1] at h
          cases hz : core.cmp.PartialEq.ne.trait_default
              field.QM31.Insts.CoreCmpPartialEqQM31 w.c1 field.QM31.ZERO with
          | fail e =>
            simp only [hz, bind_tc_fail] at h
            cases h
          | div =>
            simp only [hz, bind_tc_div] at h
            cases h
          | ok bad =>
            cases bad with
            | true =>
              simp only [hz, bind_tc_ok, ↓reduceIte] at h
              cases h
            | false =>
              simp only [hz, bind_tc_ok] at h
              change r1_wire.validate_record_fields_loop next row =
                ok (core.result.Result.Ok ()) at h
              have ih := loop_success next row h
              have hzero : w.c1 = field.QM31.ZERO := (qm31_ne_false_iff _ _).mp hz
              intro candidate hmem
              rcases List.mem_cons.mp hmem with rfl | hmem
              · exact ⟨w, hd, hzero⟩
              · exact ih candidate hmem
termination_by iter.iter.chunks.length
decreasing_by simp only [hc, List.length_cons]; omega

/-- Concrete byte/word conclusion, with no unconstrained default byte. -/
def CanonicalChunk (raw : List U8) : Prop :=
  ∃ arr : Array U8 32#usize, arr.val = raw ∧
    (∀ i : Fin 8, (wordLE arr i).val < 2147483647) ∧
    (packed (wordLE arr 0) (wordLE arr 1) (wordLE arr 2) (wordLE arr 3)
      (wordLE arr 4) (wordLE arr 5) (wordLE arr 6) (wordLE arr 7)).c1 = field.QM31.ZERO

theorem canonical_of_chunkValid (chunk : Slice U8) (h : ChunkValid chunk) :
    CanonicalChunk chunk.val := by
  rcases h with ⟨w, hd, hz⟩
  obtain ⟨_, arr, hs, hc, hp⟩ := slice_success chunk w hd
  refine ⟨arr, ?_, hc, ?_⟩
  · have he := congrArg (fun s : Slice U8 => s.val) hs
    simpa only [Array.to_slice] using he
  · rw [← hp]
    exact hz

theorem validator_chunks_success (row : U8) (payload : Slice U8)
    (ce : core.slice.iter.ChunksExact U8)
    (hce : core.slice.Slice.chunks_exact payload 32#usize = ok ce)
    (h : r1_wire.validate_record_fields row payload = ok (core.result.Result.Ok ())) :
    ∀ chunk ∈ ce.chunks, ChunkValid chunk := by
  unfold r1_wire.validate_record_fields at h
  simp only [hce, bind_tc_ok,
    core.iter.traits.iterator.Iterator.enumerate.trait_default,
    core.iter.traits.iterator.Iterator.enumerate.default] at h
  exact loop_success ⟨ce, 0#usize⟩ row h

private theorem chunks_exact_raw (payload : Slice U8)
    (ce : core.slice.iter.ChunksExact U8)
    (hce : core.slice.Slice.chunks_exact payload 32#usize = ok ce) :
    ce.chunks.map (fun chunk => chunk.val) =
      (List.toChunksExact 32 (by decide) payload.val).1 := by
  unfold core.slice.Slice.chunks_exact at hce
  simp only [show 0 < (32#usize).val from by decide, ↓reduceDIte] at hce
  have he := Result.ok.inj hce
  rw [← he]
  simp

/-- Every complete chunk returned by the actual chunk iterator is canonical
with zero high component. No conclusion is made about its ignored remainder. -/
theorem validate_record_fields_success (row : U8) (payload : Slice U8)
    (h : r1_wire.validate_record_fields row payload = ok (core.result.Result.Ok ())) :
    ∀ raw ∈ (List.toChunksExact 32 (by decide) payload.val).1, CanonicalChunk raw := by
  cases hce : core.slice.Slice.chunks_exact payload 32#usize with
  | fail e =>
    simp only [r1_wire.validate_record_fields, hce, bind_tc_fail] at h
    cases h
  | div =>
    simp only [r1_wire.validate_record_fields, hce, bind_tc_div] at h
    cases h
  | ok ce =>
    have hv := validator_chunks_success row payload ce hce h
    intro raw hraw
    have hm : raw ∈ ce.chunks.map (fun chunk => chunk.val) := by
      rw [chunks_exact_raw payload ce hce]
      exact hraw
    obtain ⟨chunk, hc, he⟩ := List.mem_map.mp hm
    simpa only [he] using canonical_of_chunkValid chunk (hv chunk hc)

end AspisR1.ExtractedRecordValidator

#print axioms AspisR1.ExtractedRecordValidator.loop_unroll
#print axioms AspisR1.ExtractedRecordValidator.loop_success
#print axioms AspisR1.ExtractedRecordValidator.canonical_of_chunkValid
#print axioms AspisR1.ExtractedRecordValidator.validator_chunks_success
#print axioms AspisR1.ExtractedRecordValidator.validate_record_fields_success
