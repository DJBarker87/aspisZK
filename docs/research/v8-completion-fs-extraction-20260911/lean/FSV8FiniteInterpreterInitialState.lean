import FSV8FiniteInterpreterBridge

/-!
# Finite fresh-answer tails after an existing oracle history

`FSV8FiniteInterpreterBridge` starts from the empty oracle.  This leaf keeps an
arbitrary existing cache/log/next state and supplies only the subsequent fresh
answer tail.  It is a deterministic continuation theorem: uniformity of that
tail conditional on a real adversarial prefix is deliberately not assumed.
-/
set_option autoImplicit false
set_option Elab.async false

namespace AspisV8Completion.FSV8FiniteInterpreterInitialState
open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open FSV8PostOODGammaScript FSV8FreshTapeBudget

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block
abbrev Tape := FSBoundedTranscript.Tape
abbrev Oracle := FSBoundedTranscript.Oracle
abbrev Point := FSV8PostOODGammaScript.Point

noncomputable section

/-- Extend a finite continuation starting at the existing fresh-call count.
    Values before the cut and beyond the supplied tail are explicit fallback
    values; the run theorem below proves neither is observed. -/
def extendFiniteTail {steps : Nat} (offset : Nat)
    (finite : Fin steps → Block) (fallback : Block) : Tape :=
  fun j => if h : offset ≤ j ∧ j - offset < steps then
    finite ⟨j - offset, h.2⟩ else fallback

def finiteInterpreterFrom {n m steps : Nat}
    (finite : Fin steps → Block) (fallback : Block)
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (body : Bytes) (digest : Block) (initial : Oracle) :=
  run (extendFiniteTail initial.next finite fallback)
    (sourceThenGammaScript firstWork secondWork body digest) initial

/-- A finite continuation gives exactly the same result as an arbitrary
    Nat-indexed tape when both agree on the fresh coordinates available after
    the existing prefix.  Cache hits, aborts and unused tail cells are covered
    by the total `run_tape_congr` proof. -/
theorem finiteInterpreterFrom_agrees_with_nat_tape
    {n m steps : Nat} (finite : Fin steps → Block) (fallback : Block)
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (body : Bytes) (digest : Block) (initial : Oracle) (tape : Tape)
    (same : ∀ (j : Nat) (hj : j < steps),
      tape (initial.next + j) = finite ⟨j, hj⟩)
    (budget : sourceThenGammaBudget n m ≤ steps) :
    finiteInterpreterFrom finite fallback firstWork secondWork body digest initial =
      run tape (sourceThenGammaScript firstWork secondWork body digest) initial := by
  apply run_tape_congr
  intro j lower upper
  have tailLtBudget : j - initial.next < sourceThenGammaBudget n m := by
    unfold sourceThenGammaBudget
    omega
  have tailLt : j - initial.next < steps :=
    lt_of_lt_of_le tailLtBudget budget
  simp only [extendFiniteTail]
  rw [dif_pos ⟨lower, tailLt⟩]
  calc
    finite ⟨j - initial.next, tailLt⟩ =
        tape (initial.next + (j - initial.next)) :=
      (same (j - initial.next) tailLt).symm
    _ = tape j := by rw [Nat.add_sub_of_le lower]

/-- The explicit conditional-continuation experiment.  A later ROM theorem
    must prove that a real prefix leaves such a uniform unused tail; this
    definition does not assert that fact. -/
noncomputable def finiteContinuationDistribution {n m steps : Nat}
    (fallback : Block)
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (body : Bytes) (digest : Block) (initial : Oracle) :=
  (PMF.uniformOfFintype (Fin steps → Block)).map fun finite =>
    finiteInterpreterFrom finite fallback firstWork secondWork body digest initial

#print axioms finiteInterpreterFrom_agrees_with_nat_tape
end
end AspisV8Completion.FSV8FiniteInterpreterInitialState
