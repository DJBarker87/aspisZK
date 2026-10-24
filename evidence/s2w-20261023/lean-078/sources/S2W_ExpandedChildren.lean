import S2W_ExpandedTrace

/-! Named per-call child source executions. Their arguments/results are the
actual typed call occurrence; there is no caller-wide observation equality,
account frame, retained input equality, or schedule conclusion in the port. -/
set_option autoImplicit false
namespace AspisR1.S2W_ExpandedChildren
open Aeneas Aeneas.Std Result S2W_Trace S2W_ExpandedTrace

structure ChildConeJoin (E : Type) (ops : AdapterRw.Ops) where
  execute : {A : Type} → Call A → Result (A × List (S2W_ExpandedTrace.Event E))
  erasure : ∀ {A : Type} (call : Call A),
    thenResult (execute call) (fun answer => ok answer.1) = invoke ops call

def events {E : Type} {ops : AdapterRw.Ops} (port : ChildConeJoin E ops) :
    S2W_Trace.Event → List (S2W_ExpandedTrace.Event E)
  | .returned call _ => match port.execute call with
    | .ok (_,log) => log
    | _ => []

def invocation {E : Type} : S2W_Trace.Event → List (S2W_ExpandedTrace.Event E)
  | .returned (.op10 _ _ _ _ _ _ _) _ => [.site .tx1]
  | .returned (.op11 _ _ _ _ _ _) _ => [.site .tx2]
  | _ => []

def children {E : Type} {ops : AdapterRw.Ops} (port : ChildConeJoin E ops)
    (event : S2W_Trace.Event) : List (S2W_ExpandedTrace.Event E) :=
  invocation event ++ events port event

/-- Actual successful source invocation determines BOTH result and internal
trace. Failed/diverging children cannot contribute an invented event list. -/
theorem returned_child {E A : Type} {ops : AdapterRw.Ops} (port : ChildConeJoin E ops)
    (call : Call A) (value : A) (valid : invoke ops call = ok value) :
    port.execute call = ok (value,events port (.returned call value)) := by
  have erased := (port.erasure call).trans valid
  cases execution : port.execute call with
  | fail error => simp only [execution,thenResult] at erased; cases erased
  | div => simp only [execution,thenResult] at erased; cases erased
  | ok answer =>
    have same : answer.1 = value := Result.ok.inj erased
    simpa only [events,execution,Prod.mk.eta,same]

/-- Full events are now computed by substituting the source trace supplied
by the child cone at each outer-call occurrence. No free pre/middle lists or
independently selected replacement traces are arguments. -/
theorem accepted_native_children {E : Type}
    (ops : AdapterRw.Ops) (native1 : S2W_ExtractionBoundary.First)
    (native2 : S2W_ExtractionBoundary.Second)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction ops native1 native2 hashv)
    (program : S2W_ExtractionBoundary.Program)
    (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts) (data1 data2 : Slice U8)
    (slot : S2W_ExtractionBoundary.Slot) (saved : alloc.vec.Vec U8)
    (accepted1 : native1 program accounts1 data1 = ok (.Ok saved))
    (accepted2 : native2 program accounts2 data2 slot = ok (.Ok ()))
    (port : ChildConeJoin E ops) :
    ∃ outer,
      run ops (S2W_Observation.two ops program accounts1 data1 accounts2 data2 slot) [] =
        ok (.Ok saved,outer) ∧
      runExpanded ops (children port)
        (S2W_Observation.two ops program accounts1 data1 accounts2 data2 slot) [] =
        ok (.Ok saved,full (children port) outer) ∧
      (∀ event ∈ outer, match event with
        | .returned call value =>
          port.execute call = ok (value,events port event)) := by
  obtain ⟨outer,execution,expanded,valid⟩ := accepted_native_flatMap ops native1 native2 hashv
    extraction program accounts1 accounts2 data1 data2 slot saved accepted1 accepted2 (children port)
  refine ⟨outer,execution,expanded,?_⟩
  intro event member
  cases event with
  | returned call value => exact returned_child port call value (valid _ member)

#print axioms returned_child
#print axioms accepted_native_children
#print ChildConeJoin
end AspisR1.S2W_ExpandedChildren
