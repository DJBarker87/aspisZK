import CanonicalLiteralEcheckRound1Success
import CanonicalLiteralEcheckChunkArray
import UnrolledWideParserRefinement

/-! The actual extracted round-1 checker, on an exact 224-byte slice, exposes
seven ordered 32-byte parser-success values. This theorem still says only what
the echeck entrypoint checked; a caller theorem must connect the relevant
View::parse section to this slice. -/
set_option autoImplicit false

namespace AspisR1.CanonicalLiteralEcheckSevenChunks
open Aeneas Aeneas.Std Result
open AspisR1.CanonicalLiteralEcheckRound1Success
open AspisR1.CanonicalLiteralEcheckChunkArray
open AspisR1.CanonicalLiteralRow30ParserAgreement

abbrev CandidateWide := AspisR1CandidateParser.field.wide_exact.WideExact

private theorem chunks32_count_local {α : Type} (xs : List α) :
    (List.toChunksExact 32 (by decide) xs).1.length = xs.length / 32 := by
  unfold List.toChunksExact
  split
  · simp
    omega
  · rename_i h
    change Nat.succ ((List.toChunksExact 32 (by decide) (xs.drop 32)).1.length) =
      xs.length / 32
    rw [chunks32_count_local (xs := xs.drop 32)]
    simp only [List.length_drop]
    omega
termination_by xs.length
decreasing_by simp only [List.length_drop]; omega

private theorem chunks_exact_raw (payload : Slice U8)
    (iter : core.slice.iter.ChunksExact U8)
    (hiter : core.slice.Slice.chunks_exact payload 32#usize = ok iter) :
    iter.chunks.map (fun chunk => chunk.val) =
      (List.toChunksExact 32 (by decide) payload.val).1 := by
  unfold core.slice.Slice.chunks_exact at hiter
  simp only [show 0 < (32#usize).val from by decide, ↓reduceDIte] at hiter
  have he := Result.ok.inj hiter
  rw [← he]
  simp

theorem seven_chunks_parsed (bytes : Slice U8)
    (hlen : bytes.val.length = 224)
    (hcheck : AspisR1EcheckCut.verifier.echeck_round1 bytes =
      ok (core.result.Result.Ok ())) :
    let chunks := (List.toChunksExact 32 (by decide) bytes.val).1
    ∃ arrays : Fin 7 → Array U8 32#usize,
      ∃ values : Fin 7 → CandidateWide,
        (∀ i : Fin 7, (arrays i).val = chunks[i.val]'(by
          rw [chunks32_count_local, hlen]
          omega)) ∧
        (∀ i : Fin 7,
          AspisR1CandidateParser.field.wide_exact.WideExact.from_le_bytes_unrolled
            (Array.to_slice (arrays i)) = ok (some (values i))) := by
  let chunks := (List.toChunksExact 32 (by decide) bytes.val).1
  change ∃ arrays : Fin 7 → Array U8 32#usize,
      ∃ values : Fin 7 → CandidateWide,
        (∀ i : Fin 7, (arrays i).val = chunks[i.val]'(by
          rw [chunks32_count_local, hlen]
          omega)) ∧
        (∀ i : Fin 7,
          AspisR1CandidateParser.field.wide_exact.WideExact.from_le_bytes_unrolled
            (Array.to_slice (arrays i)) = ok (some (values i)))
  obtain ⟨iter, hiter, hparsed⟩ := round1_success_chunks_candidate bytes hcheck
  have hchunks : chunks.length = 7 := by
    dsimp only [chunks]
    rw [chunks32_count_local, hlen]
  have hmap := chunks_exact_raw bytes iter hiter
  have hlen7 : iter.chunks.length = 7 := by
    have := (congrArg List.length hmap).trans hchunks
    simpa only [List.length_map] using this
  have hpoint (i : Fin 7) :
      ∃ arr : Array U8 32#usize, ∃ w : CandidateWide,
        arr.val = chunks[i.val]'(by rw [hchunks]; exact i.isLt) ∧
        AspisR1CandidateParser.field.wide_exact.WideExact.from_le_bytes_unrolled
          (Array.to_slice arr) = ok (some w) := by
    have hi : i.val < iter.chunks.length := by rw [hlen7]; exact i.isLt
    have hchunkBound : i.val < chunks.length := by rw [hchunks]; exact i.isLt
    let chunk : Slice U8 := iter.chunks[i.val]'(hi)
    have hmem : chunk ∈ iter.chunks := by
      exact List.getElem_mem hi
    obtain ⟨ew, hew⟩ := hparsed chunk hmem
    let w : CandidateWide := wideToCandidate ew
    obtain ⟨arr, hs, harr⟩ := slice_success_array chunk w hew
    have hslice := congrArg (fun s : Slice U8 => s.val) hs
    have hmapOpt := congrArg (fun ys : List (List U8) => ys[i.val]?) hmap
    have hmapOpt' := hmapOpt
    rw [List.getElem?_map] at hmapOpt'
    rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hchunkBound] at hmapOpt'
    have hchunkval : chunk.val = chunks[i.val]'(hchunkBound) := by
      simpa [chunk] using Option.some.inj hmapOpt'
    refine ⟨arr, w, ?_, harr⟩
    simpa [Array.to_slice] using hslice.trans hchunkval
  choose arrays values hvalues hparses using hpoint
  exact ⟨arrays, values, hvalues, hparses⟩

#print axioms seven_chunks_parsed

end AspisR1.CanonicalLiteralEcheckSevenChunks
