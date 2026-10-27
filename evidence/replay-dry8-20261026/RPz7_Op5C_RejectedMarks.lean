import RPz7_Op3I_Accepted
import VTop_Flow

set_option autoImplicit false
noncomputable section
namespace AspisR1.Op5C_RejectedMarks
open Aeneas Aeneas.Std Result

/-- Only the first transaction's actual reached batch/query/save calls count
as these sites. A rejected prefix does not acquire hypothetical suffix marks. -/
def sourceSites (log : VTop_Trace.Log) : List S2LeadInterface.Site :=
  log.filterMap fun | .returned call _ => match call with
    | .op5 _ _ _ _ _ _ => some .batch0
    | .op6 _ _ _ _ _ _ _ _ => some .query0
    | .op8 _ _ _ _ _ _ => some .save
    | _ => none

def childSites {E : Type} (log : List (S2W_ExpandedTrace.Event E)) :
    List S2LeadInterface.Site :=
  log.filterMap fun | .site site => some site | _ => none

/-- Literal extracted TX1: wrong split returns Rust Parse immediately.
The other operations, including op5, are arbitrary and never evaluated. -/
theorem source_wrong_split (ops : VTop_Stages.Ops) {Hash : Type}
    (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (semantic : VTop_Stages.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split expected : Usize)
    (obs : Option (VTop_Stages.verifier.Phase → Result Unit))
    (read : ops.op16 = ok expected) (wrong : split ≠ expected) :
    VTop_Stages.verifier.candidate.tx1 ops D semantic pub proof split hash obs =
      ok (.Err .Parse) ∧
    VTop_Trace.run ops
      (VTop_Flow.tx1 VTop_Flow.traceEffects D semantic pub proof split hash obs) [] =
      ok (.Err .Parse,[.returned .op16 expected]) ∧
    sourceSites [.returned .op16 expected] = [] := by
  have bad : (split != expected) = true := by simp [wrong]
  constructor
  · simp only [VTop_Stages.verifier.candidate.tx1, read, bind_tc_ok,
      if_pos bad]
  constructor
  · simp only [VTop_Flow.tx1, VTop_Flow.traceEffects, Bind.bind,
      VTop_Trace.bind, VTop_Trace.perform, VTop_Trace.run, VTop_Trace.invoke,
      read, VTop_Trace.thenResult, if_pos bad]
    rfl
  · rfl

/-- Existing FirstMarks quantifies over all typed events, without checking
native validity or Rust Ok. Thus even a rejected op10 must expose batch0. -/
theorem first_marks_force_batch {E : Type} {ops : AdapterRw.Ops}
    (port : S2W_ExpandedChildren.ChildConeJoin E ops)
    (marks : S2W_TraceSplice.FirstMarks port) (event : S2W_Trace.Event)
    (marked : S2W_OuterOccurrences.mark event = some false) :
    .batch0 ∈ childSites (S2W_ExpandedChildren.events port event) := by
  obtain ⟨segments, layout⟩ := marks.source event marked
  have member : S2W_SiteSchedule.Event.site .batch0 ∈
      (S2W_ExpandedChildren.events port event).map S2W_TraceSplice.project := by
    rw [layout]
    simp [S2W_SiteSchedule.firstTrace]
  obtain ⟨chosen, belongs, same⟩ := List.mem_map.mp member
  cases chosen with
  | outer x => cases same
  | child x => cases same
  | site site =>
    have equal : site = .batch0 := S2W_SiteSchedule.Event.site.inj same
    subst site
    exact List.mem_filterMap.mpr ⟨.site .batch0, belongs, rfl⟩

/-- Counterexample to a globally source-faithful installation retaining the
unconditional mark premise. This is not a counterexample to accepted-only
association, authentication, or the shipped multiproof algorithm. -/
theorem no_global_first_mark_association {E : Type} {ops : AdapterRw.Ops}
    (event : S2W_Trace.Event)
    (marked : S2W_OuterOccurrences.mark event = some false) (expected : Usize) :
    ¬ ∃ port : S2W_ExpandedChildren.ChildConeJoin E ops,
      S2W_TraceSplice.FirstMarks port ∧
      childSites (S2W_ExpandedChildren.events port event) =
        sourceSites [.returned .op16 expected] := by
  rintro ⟨port, marks, associated⟩
  have forced := first_marks_force_batch port marks event marked
  rw [associated] at forced
  exact List.not_mem_nil forced

#print axioms source_wrong_split
#print axioms first_marks_force_batch
#print axioms no_global_first_mark_association
end AspisR1.Op5C_RejectedMarks
end
