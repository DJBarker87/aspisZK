import Op5C_RejectedMarks
import VTop_Order
import Tx2I_Witness

set_option autoImplicit false
noncomputable section
namespace AspisR1.Op5T_Marks
open Aeneas Aeneas.Std Result
open S2W_ExpandedChildren S2W_TraceSplice

/-- Success is the actual invocation's Rust Ok, not a fabricated returned value. -/
def accepted (ops : AdapterRw.Ops) : S2W_Trace.Event → Prop
  | .returned (.op10 D semantic pub proof split hash obs) _ =>
      ∃ saved, ops.op10 D semantic pub proof split hash obs = ok (.Ok saved)
  | .returned (.op11 D pub proof checkpoint hash obs) _ =>
      ops.op11 D pub proof checkpoint hash obs = ok (.Ok ())
  | _ => False

/-- Lead-authorised replacement: rejected and undefined calls have no suffix
layout requirement. This is strictly an accepted-call statement. -/
structure FirstMarks {E : Type} {ops : AdapterRw.Ops} (port : ChildConeJoin E ops) : Prop where
  source : ∀ event, S2W_OuterOccurrences.mark event = some false → accepted ops event →
    ∃ fs : S2W_SiteSchedule.FirstSegments (Option E),
      (events port event).map project = S2W_SiteSchedule.firstTrace fs

structure SecondMarks {E : Type} {ops : AdapterRw.Ops} (port : ChildConeJoin E ops) : Prop where
  source : ∀ event, S2W_OuterOccurrences.mark event = some true → accepted ops event →
    ∃ ss : S2W_SiteSchedule.SecondSegments (Option E),
      (events port event).map project = S2W_SiteSchedule.secondTrace ss

theorem weaken_first {E : Type} {ops : AdapterRw.Ops} (port : ChildConeJoin E ops)
    (old : S2W_TraceSplice.FirstMarks port) : FirstMarks port :=
  ⟨fun event marked _ => old.source event marked⟩

theorem weaken_second {E : Type} {ops : AdapterRw.Ops} (port : ChildConeJoin E ops)
    (old : S2W_TraceSplice.SecondMarks port) : SecondMarks port :=
  ⟨fun event marked _ => old.source event marked⟩

/-- Site projection of the literal source ID trace. It is not a free child log. -/
def firstSite : Nat → Option S2LeadInterface.Site
  | 5 => some .batch0 | 6 => some .query0 | 8 => some .save | _ => none

theorem source_sites (log : VTop_Trace.Log) :
    Op5C_RejectedMarks.sourceSites log = (VTop_Run.ids log).filterMap firstSite := by
  induction log with
  | nil => rfl
  | cons event tail ih =>
    cases event with
    | returned call value => cases call <;>
        simp only [Op5C_RejectedMarks.sourceSites, VTop_Run.ids, List.map_cons,
          List.filterMap_cons, VTop_Trace.operationId, firstSite] at ih ⊢ <;>
        simpa using ih

/-- Accepted-run source marks are derived from the actual extracted TX1 body. -/
theorem accepted_source_marks (ops : VTop_Stages.Ops) {Hash : Type}
    (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (semantic : VTop_Stages.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize)
    (obs : Option (VTop_Stages.verifier.Phase → Result Unit)) (saved : alloc.vec.Vec U8)
    (success : VTop_Stages.verifier.candidate.tx1 ops D semantic pub proof split hash obs = ok (.Ok saved)) :
    ∃ log, VTop_Trace.run ops (VTop_Flow.tx1 VTop_Flow.traceEffects D semantic pub proof split hash obs) [] =
      ok (.Ok saved,log) ∧ Op5C_RejectedMarks.sourceSites log = [.batch0,.query0,.save] := by
  obtain ⟨log,run,order⟩ := VTop_Order.accepted_tx1 ops D hash semantic pub proof split obs saved success
  exact ⟨log,run,by rw [source_sites,order]; rfl⟩

#print axioms weaken_first
#print axioms weaken_second
#print axioms source_sites
#print axioms accepted_source_marks
end AspisR1.Op5T_Marks
end
