import FSV7OODSampler
import FSV8OODBodyScript
set_option autoImplicit false
set_option Elab.async false
namespace AspisV8Completion.FSV7OODBodyScript
open FSOracleExecution FSBoundedTranscript FSTranscriptScript FSOODSampler
open FSV7OODSampler FSV8OODBodyScript

abbrev Point := AspisK1.V7Tag73DeterministicRefinement.SecureCirclePointBytes
abbrev Result := PairResult (Point := Point)
noncomputable section
local instance : DecidableEq Point := Classical.decEq _

/-- Concrete source slice: there is no abstract point decoder left.  This is
the reviewed V7 four-limb tower assembly, inverse-before-subfield-check circle
map, and literal three-by-three retry policy. -/
def sourceScript {n m : Nat}
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (body : Bytes) (digest : Block) :=
  checkedBodyPairScript decodePoint firstWork secondWork body digest

theorem successful_source_is_canonical {n m : Nat}
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (body : Bytes) (digest : Block) (tape : Tape) (oracle : Oracle)
    (result : Except Error Result × Block)
    (success : (run tape (sourceScript firstWork secondWork body digest) oracle).1 = some result) :
    CanonicalOODFields body :=
  checked_success_canonical decodePoint firstWork secondWork body digest tape oracle result success

theorem successful_source_points_distinct {n m : Nat}
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (body : Bytes) (digest : Block) (tape : Tape) (oracle : Oracle)
    (out : Result) (finalDigest : Block)
    (success : (run tape (sourceScript firstWork secondWork body digest) oracle).1 =
      some (.ok out, finalDigest)) :
    out.second ≠ out.first := by
  unfold sourceScript checkedBodyPairScript at success
  split at success
  · unfold bodyPairScript at success
    rw [run_bind] at success
    have firstExact := run_circle decodePoint tape 3
      { digest := digest, oracle := oracle }
    change run tape (circleScript decodePoint 3 digest) oracle = _ at firstExact
    rw [firstExact] at success
    cases hfirst : (circle decodePoint tape 3
        { digest := digest, oracle := oracle }).1 with
    | error e =>
        simp only [hfirst, run] at success
        cases success
    | ok firstPoint =>
        simp only [hfirst] at success
        rw [run_bind, run_answerScript] at success
        cases hfirstWork : (run tape (firstWork firstPoint)
            (circle decodePoint tape 3
              { digest := digest, oracle := oracle }).2.oracle).1 with
        | none =>
            simp only [hfirstWork, Option.map_none] at success
            cases success
        | some firstUnit =>
            simp only [hfirstWork, Option.map_some] at success
            rw [run_bind] at success
            rw [run_absorb tape
              { digest := (circle decodePoint tape 3
                  { digest := digest, oracle := oracle }).2.digest,
                oracle := (run tape (firstWork firstPoint)
                  (circle decodePoint tape 3
                    { digest := digest, oracle := oracle }).2.oracle).2 }] at success
            simp only [] at success
            rw [run_bind, run_distinct] at success
            let afterFirst := absorb tape
              { digest := (circle decodePoint tape 3
                  { digest := digest, oracle := oracle }).2.digest,
                oracle := (run tape (firstWork firstPoint)
                  (circle decodePoint tape 3
                    { digest := digest, oracle := oracle }).2.oracle).2 }
              62 (0 :: answerBytes body 0)
            cases hsecond : (distinct decodePoint firstPoint tape 3 afterFirst).1 with
            | error e =>
                dsimp [afterFirst] at hsecond
                simp only [hsecond, afterSecond, run] at success
                cases success
            | ok secondPoint =>
                dsimp [afterFirst] at hsecond
                simp only [hsecond, afterSecond] at success
                rw [run_bind, run_answerScript] at success
                cases hsecondWork : (run tape (secondWork firstPoint secondPoint)
                    (distinct decodePoint firstPoint tape 3 afterFirst).2.oracle).1 with
                | none =>
                    dsimp [afterFirst] at hsecondWork
                    simp only [hsecondWork, Option.map_none] at success
                    cases success
                | some secondUnit =>
                    dsimp [afterFirst] at hsecondWork
                    simp only [hsecondWork, Option.map_some] at success
                    rw [run_bind] at success
                    have secondAbsorbExact := run_absorb tape
                      { digest := (distinct decodePoint firstPoint tape 3 afterFirst).2.digest,
                        oracle := (run tape (secondWork firstPoint secondPoint)
                          (distinct decodePoint firstPoint tape 3 afterFirst).2.oracle).2 }
                      62 (1 :: answerBytes body 1)
                    dsimp [afterFirst] at secondAbsorbExact
                    rw [secondAbsorbExact] at success
                    simp only [run] at success
                    cases success
                    exact second_success_distinct firstPoint secondPoint tape afterFirst hsecond
  · contradiction

/-- Every V7 sampler retry, answer-builder call, answer absorption and abort is
part of one append-only oracle execution. -/
theorem source_prefix {n m : Nat}
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (body : Bytes) (digest : Block) (tape : Tape) (oracle : Oracle) :
    Prefix oracle (run tape (sourceScript firstWork secondWork body digest) oracle).2 := by
  simpa only [Prefix] using run_extends tape
    (sourceScript firstWork secondWork body digest) oracle

theorem source_valid {n m : Nat}
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (body : Bytes) (digest : Block) (tape : Tape) (oracle : Oracle)
    (valid : FSFirstFresh.ValidHistory oracle) :
    FSFirstFresh.ValidHistory
      (run tape (sourceScript firstWork secondWork body digest) oracle).2 :=
  FSFirstFresh.run_valid tape _ oracle valid

theorem source_call_allowance {n m : Nat}
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (body : Bytes) (digest : Block) (tape : Tape) (oracle : Oracle) :
    (run tape (sourceScript firstWork secondWork body digest) oracle).2.log.length ≤
      oracle.log.length + (((1+m)+594+1+n)+198) :=
  call_bound tape _ oracle

theorem first_record_size (body : Bytes) : (0 :: answerBytes body 0).length = 465 := by
  simpa using answer_bytes_size body 0

theorem second_record_size (body : Bytes) : (1 :: answerBytes body 1).length = 465 := by
  simpa using answer_bytes_size body 1

/- These are deterministic execution and shape facts.  The existing
`second_success_distinct` theorem applies to the concrete distinct sampler;
this leaf does not assert any distribution, cache-miss or fresh-exposure law. -/
#print axioms successful_source_is_canonical
#print axioms successful_source_points_distinct
#print axioms source_prefix
#print axioms source_valid
#print axioms source_call_allowance
#print axioms first_record_size
#print axioms second_record_size
end
end AspisV8Completion.FSV7OODBodyScript
