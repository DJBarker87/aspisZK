import FSV8PostOODGammaScript
import FSFreshTapeTrace

set_option autoImplicit false
set_option Elab.async false

namespace AspisV8Completion.FSV8FreshTapeBudget
open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open FSV8PostOODGammaScript FSFreshTapeTrace

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block
abbrev Tape := FSBoundedTranscript.Tape
abbrev Oracle := FSBoundedTranscript.Oracle
abbrev Point := FSV8PostOODGammaScript.Point

def sourceThenGammaBudget (n m : Nat) : Nat :=
  (1 + 3 * 66) + (((1 + m) + 594 + 1 + n) + 198)

theorem sourceThenGamma_log_bound {n m : Nat}
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (body : Bytes) (digest : Block) (tape : Tape) (oracle : Oracle) :
    (run tape (sourceThenGammaScript firstWork secondWork body digest) oracle).2.log.length ≤
      oracle.log.length + sourceThenGammaBudget n m := by
  exact call_bound tape _ _

/-- From the empty lazy oracle, the number of fresh answers consumed by the
    whole composed source script is bounded by its static script budget.  This
    is a trace/cardinality fact only: it makes no independence or probability
    claim. -/
theorem sourceThenGamma_fresh_budget {n m : Nat}
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (body : Bytes) (digest : Block) (tape : Tape) :
    (run tape (sourceThenGammaScript firstWork secondWork body digest)
      (FSFirstFresh.empty : Oracle)).2.next ≤ sourceThenGammaBudget n m := by
  let final := run tape (sourceThenGammaScript firstWork secondWork body digest)
    (FSFirstFresh.empty : Oracle)
  have trace := run_from_empty_matches tape
    (sourceThenGammaScript firstWork secondWork body digest)
  unfold MatchesTape at trace
  have hlen : final.2.next = (freshAnswers final.2.log).length := by
    have lengths := congrArg List.length trace
    simpa [final, FSFirstFresh.empty] using lengths.symm
  have hfilter : (freshAnswers final.2.log).length ≤ final.2.log.length := by
    unfold freshAnswers
    exact List.length_filterMap_le
      (fun event : Event Bytes Block =>
        if event.fresh then some event.answer else none)
      final.2.log
  have hlog : final.2.log.length ≤ sourceThenGammaBudget n m := by
    have h := sourceThenGamma_log_bound firstWork secondWork body digest tape
      (FSFirstFresh.empty : Oracle)
    simpa only [final, FSFirstFresh.empty, List.length_nil, zero_add] using h
  change final.2.next ≤ sourceThenGammaBudget n m
  calc
    final.2.next = (freshAnswers final.2.log).length := hlen
    _ ≤ final.2.log.length := hfilter
    _ ≤ sourceThenGammaBudget n m := hlog

#print axioms sourceThenGamma_log_bound
#print axioms sourceThenGamma_fresh_budget
end AspisV8Completion.FSV8FreshTapeBudget
