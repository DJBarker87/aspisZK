import CanonicalLiteralEcheckLoopSuccess
import CanonicalLiteralRow30ParserAgreement

/-! Successful echeck_round1 return implies every complete 32-byte iterator
chunk was parsed as a canonical WideExact. This is still an iterator-level
fact: a separate caller theorem must connect a `View::parse` byte section to
this slice and its seven chunks. -/
set_option autoImplicit false

namespace AspisR1.CanonicalLiteralEcheckRound1Success
open Aeneas Aeneas.Std Result
open AspisR1.CanonicalLiteralEcheckLoopSuccess
open AspisR1.CanonicalLiteralRow30ParserAgreement

abbrev EcheckIter := core.slice.iter.ChunksExact U8

theorem round1_success_chunks (bytes : Slice U8)
    (h : AspisR1EcheckCut.verifier.echeck_round1 bytes =
      ok (core.result.Result.Ok ())) :
    ∃ iter : EcheckIter,
      core.slice.Slice.chunks_exact bytes 32#usize = ok iter ∧
      ∀ chunk ∈ iter.chunks, Parses chunk := by
  unfold AspisR1EcheckCut.verifier.echeck_round1
    AspisR1EcheckCut.verifier.echeck at h
  cases hc : core.slice.Slice.chunks_exact bytes 32#usize with
  | fail e =>
    have hf : False := by simp [hc, bind_tc_fail] at h
    exact hf.elim
  | div =>
    have hf : False := by simp [hc, bind_tc_div] at h
    exact hf.elim
  | ok iter =>
    simp only [hc, bind_tc_ok] at h
    refine ⟨iter, rfl, ?_⟩
    exact fun chunk hmem => loop_success iter h chunk hmem

/-- Transfer each actual generated echeck parser success through the explicit
carrier map to the retained Candidate parser. -/
theorem round1_success_chunks_candidate (bytes : Slice U8)
    (h : AspisR1EcheckCut.verifier.echeck_round1 bytes =
      ok (core.result.Result.Ok ())) :
    ∃ iter : EcheckIter,
      core.slice.Slice.chunks_exact bytes 32#usize = ok iter ∧
      ∀ chunk ∈ iter.chunks, ∃ w : EcheckWide,
        AspisR1CandidateParser.field.wide_exact.WideExact.from_le_bytes_unrolled
          chunk = ok (some (wideToCandidate w)) := by
  obtain ⟨iter, hit, hchunks⟩ := round1_success_chunks bytes h
  refine ⟨iter, hit, ?_⟩
  intro chunk hmem
  obtain ⟨w, hw⟩ := hchunks chunk hmem
  exact ⟨w, actual_success_to_candidate_success chunk w hw⟩

#print axioms round1_success_chunks
#print axioms round1_success_chunks_candidate

end AspisR1.CanonicalLiteralEcheckRound1Success
