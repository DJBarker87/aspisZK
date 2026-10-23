import S2W_AccountObservations

/-! Expansion at EVERY typed call occurrence in the actual outer log. The
same evaluator calls the same Ops in the same order; expansion is only an
observation, never a second child execution or an invented query schedule. -/
set_option autoImplicit false
namespace AspisR1.S2W_ExpandedTrace
open Aeneas Aeneas.Std Result S2W_Trace

inductive Event (E : Type) : Type 1 where
  | outer (event : S2W_Trace.Event)
  | child (event : E)
  | site (site : S2LeadInterface.Site)

/-- Children remain individually indexed to the actual typed outer event.
No byte serialization or call-number equality replaces the arguments/result. -/
def expand {E : Type} (children : S2W_Trace.Event → List (Event E))
    (event : S2W_Trace.Event) : List (Event E) := .outer event :: children event

def full {E : Type} (children : S2W_Trace.Event → List (Event E))
    (outer : Log) : List (Event E) := outer.flatMap (expand children)

def runExpanded {E A : Type} (ops : AdapterRw.Ops)
    (children : S2W_Trace.Event → List (Event E)) :
    Code A → List (Event E) → Result (A × List (Event E))
  | .done a, log => ok (a,log)
  | .step r k, log => thenResult r (fun b => runExpanded ops children (k b) log)
  | .call op k, log => thenResult (invoke ops op) (fun b =>
      runExpanded ops children (k b) (log ++ expand children (.returned op b)))

/-- All successful outer executions expand by flatMap, including outer events
before, between and after the two verifier calls. This proof is independent
of source acceptance and is valid on any observed returning prefix. -/
theorem execution_flatMap {E A : Type} (ops : AdapterRw.Ops)
    (children : S2W_Trace.Event → List (Event E)) (code : Code A)
    (before after : Log) (result : A)
    (execution : run ops code before = ok (result,after)) :
    runExpanded ops children code (full children before) = ok (result,full children after) := by
  induction code generalizing before after with
  | done a =>
    have same := Result.ok.inj execution
    cases same
    rfl
  | step r k ih =>
    cases r with
    | fail e => cases execution
    | div => cases execution
    | ok b => exact ih b before after execution
  | call op k ih =>
    cases invoked : invoke ops op with
    | fail e => simp only [run,thenResult,invoked] at execution; cases execution
    | div => simp only [run,thenResult,invoked] at execution; cases execution
    | ok b =>
      simp only [run,thenResult,invoked] at execution
      simpa only [runExpanded,invoked,thenResult,full,List.flatMap_append,
        List.flatMap_cons,List.flatMap_nil,List.append_nil] using
        ih b (before ++ [.returned op b]) after execution

/-- An occurrence-based splice law. e1 and e2 are the actual typed returns,
not just identifiers; all prefix/middle/suffix outer events are retained. -/
theorem splice {E : Type} (children : S2W_Trace.Event → List (Event E))
    (outer pre middle post : Log) (e1 e2 : S2W_Trace.Event)
    (occurrences : outer = pre ++ [e1] ++ middle ++ [e2] ++ post) :
    full children outer = full children pre ++ expand children e1 ++
      full children middle ++ expand children e2 ++ full children post := by
  simp only [occurrences,full,List.flatMap_append,List.flatMap_cons,
    List.flatMap_nil,List.append_nil]

/-- The exact accepted native outer execution, expanded at each call. No
independent timeline is existentially selected. Child trace interpretation
and source marks still belong to the separate named child cone joins. -/
theorem accepted_native_flatMap {E : Type}
    (ops : AdapterRw.Ops) (native1 : S2W_ExtractionBoundary.First)
    (native2 : S2W_ExtractionBoundary.Second)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction ops native1 native2 hashv)
    (program : S2W_ExtractionBoundary.Program)
    (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts) (data1 data2 : Slice U8)
    (slot : S2W_ExtractionBoundary.Slot) (saved : alloc.vec.Vec U8)
    (accepted1 : native1 program accounts1 data1 = ok (.Ok saved))
    (accepted2 : native2 program accounts2 data2 slot = ok (.Ok ()))
    (children : S2W_Trace.Event → List (Event E)) :
    ∃ outer,
      run ops (S2W_Observation.two ops program accounts1 data1 accounts2 data2 slot) [] =
        ok (.Ok saved,outer) ∧
      runExpanded ops children (S2W_Observation.two ops program accounts1 data1 accounts2 data2 slot) [] =
        ok (.Ok saved,full children outer) ∧
      (∀ event ∈ outer, S2W_TraceFacts.ValidEvent ops event) := by
  obtain ⟨_,outer,_,_,_,execution,_,valid⟩ := S2W_ExtractionBoundary.accepted_native_observation
    ops native1 native2 hashv (S2W_DigestExtraction.sourceBoundary ops native1 native2 hashv extraction)
    program accounts1 accounts2 data1 data2 slot saved accepted1 accepted2
  exact ⟨outer,execution,execution_flatMap ops children _ [] outer _ execution,valid⟩

#print axioms execution_flatMap
#print axioms splice
#print axioms accepted_native_flatMap
end AspisR1.S2W_ExpandedTrace
