import FSLiveChallengeTrace

set_option autoImplicit false

namespace AspisV8Completion.FSV8CandidateOriginTrace
open FSOracleExecution FSBoundedTranscript FSLiveChallengeTrace

def outputInput (s : Transcript) : List UInt8 := List.ofFn s.digest ++ [1]

def advanceInput (s : Transcript) : List UInt8 := List.ofFn s.digest ++ [2]

/- The answer is indexed by the actual query answer, so this is a pre-query
   classification rather than a post-hoc label on an event. -/
inductive AnswerDisposition (tape : Tape) (s : Oracle) (input : List UInt8)
    (answer : Block) : Prop where
  | cacheHit (cached : Block)
      (cache : s.cache input = some cached)
      (answerEq : answer = cached)
  | fresh (cache : s.cache input = none)
      (answerEq : answer = tape s.next)

theorem answerDisposition_complete (tape : Tape) (s : Oracle)
    (input : List UInt8) :
    AnswerDisposition tape s input (query tape s input).1 := by
  cases h : s.cache input with
  | some cached =>
      exact .cacheHit cached h (by simp [query, h])
  | none =>
      exact .fresh h (by simp [query, h])

theorem answerDisposition_exhaustive (tape : Tape) (s : Oracle)
    (input : List UInt8) :
    ∃ answer, AnswerDisposition tape s input answer := by
  exact ⟨(query tape s input).1, answerDisposition_complete tape s input⟩

def outputStep (tape : Tape) (s : Transcript) :=
  query tape s.oracle (outputInput s)

def advanceStep (tape : Tape) (s : Transcript) :=
  query tape (outputStep tape s).2 (advanceInput s)

/-- The classified pair is definitionally the pair consumed by the selected
transcript squeeze.  In particular the advance input uses the original
pre-squeeze digest, not the output block. -/
theorem squeeze_eq_classified_steps (tape : Tape) (s : Transcript) :
    squeeze tape s =
      ((outputStep tape s).1,
        { digest := (advanceStep tape s).1
          oracle := (advanceStep tape s).2 }) := by
  rfl

/- The second query is indexed by the oracle state produced by the first
   query, while its byte input retains the original pre-squeeze digest. -/
inductive SqueezePairDisposition (tape : Tape) (s : Transcript) : Prop where
  | pair
      (output : AnswerDisposition tape s.oracle (outputInput s)
        (outputStep tape s).1)
      (advance : AnswerDisposition tape
        (outputStep tape s).2
        (advanceInput s)
        (advanceStep tape s).1)

theorem squeezePairDisposition_complete (tape : Tape) (s : Transcript) :
    SqueezePairDisposition tape s := by
  exact .pair
    (answerDisposition_complete tape s.oracle (outputInput s))
    (answerDisposition_complete tape (outputStep tape s).2
      (advanceInput s))

inductive OriginSqueezePath (tape : Tape) : Transcript → List Block → Transcript → Prop
  | nil (start : Transcript) : OriginSqueezePath tape start [] start
  | snoc {start current : Transcript} {blocks : List Block}
      (path : OriginSqueezePath tape start blocks current)
      (disposition : SqueezePairDisposition tape current) :
      OriginSqueezePath tape start
        (blocks ++ [(squeeze tape current).1])
        (squeeze tape current).2

theorem origin_of_squeezePath (tape : Tape) (start : Transcript) :
    ∀ {blocks : List Block} {current : Transcript},
      SqueezePath tape start blocks current →
        OriginSqueezePath tape start blocks current := by
  intro blocks current path
  induction path with
  | nil => exact .nil _
  | @snoc current blocks path ih =>
      exact .snoc ih (squeezePairDisposition_complete tape current)

theorem challenge_originSqueezePath (tape : Tape) (s : Transcript) :
    OriginSqueezePath tape s (FSLiveChallengeTrace.challenge tape s).blocks
      (FSLiveChallengeTrace.challenge tape s).final := by
  exact origin_of_squeezePath tape s (challenge_squeezePath tape s)

#print axioms answerDisposition_complete
#print axioms squeeze_eq_classified_steps
#print axioms squeezePairDisposition_complete
#print axioms origin_of_squeezePath
#print axioms challenge_originSqueezePath

end AspisV8Completion.FSV8CandidateOriginTrace
