import Mathlib.Data.Option.Basic

/-!
Reviewed-pack table draft, adapted only to use a focused import.
This is table-safety only, not a random-oracle distribution theorem.
Instantiate `Answer` with full 256-bit answers, not truncated Merkle digests.
-/
namespace AspisV8PairedCommitment

variable {Input Answer : Type*} [DecidableEq Input] [DecidableEq Answer]

abbrev Table (Input Answer : Type*) := Input → Option Answer

def Extends (old new : Table Input Answer) : Prop :=
  ∀ input answer, old input = some answer → new input = some answer

abbrev Fits (table : Table Input Answer) (input : Input) (answer : Answer) : Prop :=
  table input = none ∨ table input = some answer

def put (table : Table Input Answer) (input : Input) (answer : Answer) :
    Table Input Answer :=
  fun query => if query = input then some answer else table query

theorem extends_refl (table : Table Input Answer) : Extends table table := by
  intro input answer found
  exact found

theorem extends_trans {a b c : Table Input Answer}
    (ab : Extends a b) (bc : Extends b c) : Extends a c := by
  intro input answer found
  exact bc input answer (ab input answer found)

theorem put_extends (table : Table Input Answer) (input : Input) (answer : Answer)
    (fits : Fits table input answer) : Extends table (put table input answer) := by
  intro query old found
  by_cases same : query = input
  · subst query
    rcases fits with missing | installed
    · rw [missing] at found
      cases found
    · have values : answer = old := Option.some.inj (installed.symm.trans found)
      simp [put, values]
  · simpa [put, same] using found

/-- Both checks use the pre-update table. Tags guarantee distinct inputs in V8. -/
def installPair (table : Table Input Answer) (i j : Input) (a b : Answer) :
    Table Input Answer × Bool :=
  if i ≠ j ∧ Fits table i a ∧ Fits table j b then
    (put (put table i a) j b, true)
  else (table, false)

/-- Rejection changes no table entry. This is sequential atomicity. -/
theorem rejected_pair_unchanged (table : Table Input Answer)
    (i j : Input) (a b : Answer)
    (failed : (installPair table i j a b).2 = false) :
    (installPair table i j a b).1 = table := by
  by_cases safe : i ≠ j ∧ Fits table i a ∧ Fits table j b
  · simp [installPair, safe] at failed
  · simp [installPair, safe]

/-- A successful batch preserves prior answers and installs both full answers. -/
theorem accepted_pair_is_safe (table : Table Input Answer)
    (i j : Input) (a b : Answer)
    (success : (installPair table i j a b).2 = true) :
    Extends table (installPair table i j a b).1 ∧
      (installPair table i j a b).1 i = some a ∧
      (installPair table i j a b).1 j = some b := by
  by_cases safe : i ≠ j ∧ Fits table i a ∧ Fits table j b
  · rcases safe with ⟨different, fitI, fitJ⟩
    have fitJAfter : Fits (put table i a) j b := by
      simpa [Fits, put, Ne.symm different] using fitJ
    have extension := extends_trans (put_extends table i a fitI)
      (put_extends (put table i a) j b fitJAfter)
    simpa [installPair, different, fitI, fitJ] using
      (show Extends table (put (put table i a) j b) ∧
          put (put table i a) j b i = some a ∧
          put (put table i a) j b j = some b from
        ⟨extension, by simp [put, different], by simp [put]⟩)
  · simp [installPair, safe] at success

/-- Subsequent ordinary append-only evolution cannot invalidate the pairing. -/
theorem paired_answers_persist {before after : Table Input Answer}
    {i j : Input} {a b : Answer}
    (extension : Extends before after)
    (first : before i = some a) (second : before j = some b) :
    after i = some a ∧ after j = some b :=
  ⟨extension i a first, extension j b second⟩

#print axioms accepted_pair_is_safe
#print axioms rejected_pair_unchanged
#print axioms paired_answers_persist
end AspisV8PairedCommitment
