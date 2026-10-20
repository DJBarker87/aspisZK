import Aeneas
import QueryValidatorGeneratedPrefix
import QueryValidatorFinalFacts
import AspisR1Stage2AdoptedReader.QueryReaderSuccess
open Aeneas Aeneas.Std Result AspisR1Stage2AdoptedResume
namespace AspisR1.QueryValidatorReaderComposition
abbrev QueryArray := Array Std.U32 22#usize

/-- The reader's explicit validation boundary, specialized to the actual verifier.
    On success it returns the same array supplied to the verifier. -/
def verifierValidatorAdapter (queries : QueryArray) :
    Result (core.result.Result QueryArray verifier.Error) :=
  match verifier.validate_queries queries with
  | ok (core.result.Result.Ok ()) => ok (core.result.Result.Ok queries)
  | ok (core.result.Result.Err e) => ok (core.result.Result.Err e)
  | fail e => fail e
  | div => div

theorem verifierValidatorAdapter_success
    (input output : QueryArray)
    (h : verifierValidatorAdapter input = ok (core.result.Result.Ok output)) :
    verifier.validate_queries input = ok (core.result.Result.Ok ()) ∧ output = input := by
  unfold verifierValidatorAdapter at h
  cases hactual : verifier.validate_queries input with
  | ok result =>
      cases result with
      | Ok unit =>
          cases unit
          simp only [hactual, bind_tc_ok] at h
          exact ⟨by simpa using hactual, by simpa only [core.result.Result.Ok.injEq] using (Result.ok.inj h).symm⟩
      | Err e => simp [hactual] at h
  | fail e => simp [hactual] at h
  | div => simp [hactual] at h

/-- A successful explicit-reader call to the concrete verifier gives exactly 22
    in-range, pairwise-distinct values. The same array validated is the returned
    query array, and the reader cursor advances by the exact 88-byte schedule. -/
theorem reader_success_validates_returned_queries
    (bytes : Slice Std.U8) (cursor0 : Usize) (queries : QueryArray) (finalAt : Usize)
    (hread : verifier.resume_read_queries verifierValidatorAdapter bytes cursor0 =
      ok (core.result.Result.Ok (queries, finalAt))) :
    ∃ input : QueryArray,
      verifier.validate_queries input = ok (core.result.Result.Ok ()) ∧
      input = queries ∧
      (∀ i : Nat, i < 22 → AspisR1.QueryValidatorLoopInvariant.queryValue queries i < 2^18) ∧
      List.Pairwise (fun x y : Nat => x ≠ y)
        (AspisR1.QueryValidatorFinalFacts.queryValueList queries) ∧
      finalAt.val = cursor0.val + 88 := by
  have hreader := AspisR1Stage2AdoptedReader.QueryReaderSuccess.successful_query_read_exposes_validation_call
    verifierValidatorAdapter bytes cursor0 queries finalAt hread
  rcases hreader with ⟨_, _, q0, _, _, q1, _, _, q2, _, _, q3, _, _, q4, _, _, q5, _, _, q6, _, _, q7, _, _, q8, _, _, q9, _, _, q10, _, _, q11, _, _, q12, _, _, q13, _, _, q14, _, _, q15, _, _, q16, _, _, q17, _, _, q18, _, _, q19, _, _, q20, _, _, q21, hparts⟩
  have hneeded := hparts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  rcases hneeded with ⟨hcall, hcursor, hadvance⟩
  let input : QueryArray := Array.make 22#usize
    [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21]
  have hcall' : verifierValidatorAdapter input = ok (core.result.Result.Ok queries) := by
    simpa [input] using hcall
  obtain ⟨hvalidate, hsame⟩ := verifierValidatorAdapter_success input queries hcall'
  have hfacts := AspisR1.QueryValidatorFinalFacts.validate_queries_success_range_pairwise input hvalidate
  have hsameInput : input = queries := hsame.symm
  subst queries
  exact ⟨input, hvalidate, rfl, hfacts.1, hfacts.2, hadvance⟩

#print axioms verifierValidatorAdapter_success
#print axioms reader_success_validates_returned_queries
end AspisR1.QueryValidatorReaderComposition
