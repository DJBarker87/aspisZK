import FSV8FreshTapeBudget
import FSNonzeroSqueezeExposure

set_option autoImplicit false
set_option Elab.async false

namespace AspisV8Completion.FSV8FiniteTapePrefix
open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open FSFreshTapeTrace FSV8PostOODGammaScript FSV8FreshTapeBudget

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block
abbrev Tape := FSBoundedTranscript.Tape
abbrev Oracle := FSBoundedTranscript.Oracle
abbrev Point := FSV8PostOODGammaScript.Point

/-- Exact finite-tape embedding for one realised composed execution.  The
    consumed fresh answers are precisely the initial finite prefix of the
    supplied tape; the prefix length is bounded by the script budget.  This
    is deterministic trace bookkeeping and makes no law or probability claim.
-/
theorem sourceThenGamma_consumed_prefix {n m : Nat}
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (body : Bytes) (digest : Block) (tape : Tape) :
    let final := run tape
      (sourceThenGammaScript firstWork secondWork body digest)
      (FSFirstFresh.empty : Oracle)
    freshAnswers final.2.log = (List.range final.2.next).map tape ∧
      final.2.next ≤ sourceThenGammaBudget n m := by
  let final := run tape
    (sourceThenGammaScript firstWork secondWork body digest)
    (FSFirstFresh.empty : Oracle)
  have trace := run_from_empty_matches tape
    (sourceThenGammaScript firstWork secondWork body digest)
  have bound := sourceThenGamma_fresh_budget firstWork secondWork body digest tape
  exact ⟨trace, by simpa [final] using bound⟩

/-- The same bridge packaged as a bounded finite-tape witness, suitable as the
    deterministic premise for a later finite-tape transport theorem. -/
theorem sourceThenGamma_finite_tape_witness {n m : Nat}
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (body : Bytes) (digest : Block) (tape : Tape) :
    ∃ k : Nat, k ≤ sourceThenGammaBudget n m ∧
      freshAnswers
        (run tape (sourceThenGammaScript firstWork secondWork body digest)
          (FSFirstFresh.empty : Oracle)).2.log =
        (List.range k).map tape := by
  let final := run tape
    (sourceThenGammaScript firstWork secondWork body digest)
    (FSFirstFresh.empty : Oracle)
  obtain ⟨exactPrefix, bounded⟩ :=
    sourceThenGamma_consumed_prefix firstWork secondWork body digest tape
  exact ⟨final.2.next, bounded, exactPrefix⟩

#print axioms sourceThenGamma_consumed_prefix
#print axioms sourceThenGamma_finite_tape_witness
end AspisV8Completion.FSV8FiniteTapePrefix
