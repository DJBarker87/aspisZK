import RPz7_Uni_Install
import RPz7_Op5T_Fixture
import VTop_SecondOrder
set_option autoImplicit false
noncomputable section
namespace AspisR1.Uni_SecondMarks
open Aeneas Aeneas.Std Result

/-- Operation IDs in the literal TX2 child; sites are actual invocations. -/
def secondSite : Nat → Option S2LeadInterface.Site
  | 18 => some .resume | 5 => some .batch1 | 6 => some .query1
  | 19 => some .finish | _ => none

def sourceSites (log : VTop_Trace.Log) := (VTop_Run.ids log).filterMap secondSite

attribute [local irreducible] VTop_Flow.tx2_common

theorem authenticated_order (ops : VTop_Stages.Ops) {Hash : Type}
    (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (pub proof checkpoint : Slice U8) (obs : Option (VTop_Stages.verifier.Phase → Result Unit))
    (log : VTop_Trace.Log)
    (success : VTop_Trace.run ops
      (VTop_Flow.tx2_authenticated VTop_Flow.traceEffects D pub proof checkpoint hash obs) [] =
        ok (.Ok (),log)) :
    VTop_Run.ids log = [3,13] ++ VTop_SecondOrder.commonSchedule := by
  unfold VTop_Flow.tx2_authenticated at success
  repeat' first
  | (solve | cases success)
  | (fail_if_no_progress simp only [VTop_Trace.run,VTop_Trace.bind,VTop_Trace.perform,
      VTop_Flow.traceEffects,VTop_Trace.thenResult,VTop_Trace.liftResult] at success)
  | uncase_result
  | head_reduce success
  | split at success
  all_goals
    have order := VTop_SecondOrder.common_order ops D hash pub proof checkpoint obs _ log success
    simpa only [VTop_Run.ids,List.map_append,List.map_cons,List.map_nil,VTop_Trace.operationId,
      List.append_assoc,List.cons_append,List.nil_append] using order

/-- Every actually successful authenticated TX2 has all four source sites.
No success assumption is imposed on rejected invocations. -/
theorem accepted_source_marks (ops : VTop_Stages.Ops) {Hash : Type}
    (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (pub proof checkpoint : Slice U8) (obs : Option (VTop_Stages.verifier.Phase → Result Unit))
    (success : VTop_Stages.verifier.candidate.tx2_authenticated ops D pub proof checkpoint hash obs =
      ok (.Ok ())) :
    ∃ log, VTop_Trace.run ops
      (VTop_Flow.tx2_authenticated VTop_Flow.traceEffects D pub proof checkpoint hash obs) [] =
        ok (.Ok (),log) ∧ sourceSites log = [.resume,.batch1,.query1,.finish] := by
  obtain ⟨log,run⟩ := VTop_Run.accepted_execution ops
    (VTop_Flow.tx2_authenticated VTop_Flow.traceEffects D pub proof checkpoint hash obs) [] (.Ok ())
    ((VTop_Erasure.tx2_authenticated_erasure ops D hash pub proof checkpoint obs).trans success)
  exact ⟨log,run,by
    rw [sourceSites,authenticated_order ops D hash pub proof checkpoint obs log run]
    rfl⟩

/-- Successful SOURCE CONTROL fixture with installed shape and finish.
The remaining leaves are explicit test choices, not deployed-body proofs. -/
theorem successful_fixture (base : VTop_Stages.Ops) (x : AspisR1Stage2.Stage2Finish.E)
    (p : AspisR1Stage2.verifier.Prepared) (a : AspisR1Stage2.verifier.Accumulator)
    (geometry : AspisR1Stage2.verifier.QueryGeometry) (pending : AspisR1Stage2.verifier.BatchedWeights)
    {Hash : Type} (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (pub checkpoint : Slice U8) :
    ∃ log, VTop_Trace.run
      (Tx2I_Install.stage (Tx2I_Witness.fixture base x p a geometry pending) (Tx2I_Nonvacuity.leaves x))
      (VTop_Flow.tx2_authenticated VTop_Flow.traceEffects D pub Op3I_Witness.proof checkpoint hash none) [] =
        ok (.Ok (),log) ∧ sourceSites log = [.resume,.batch1,.query1,.finish] :=
  accepted_source_marks _ D hash pub _ checkpoint none
    (Tx2I_Witness.authenticated_success base x p a geometry pending D hash pub checkpoint)

#print axioms authenticated_order
#print axioms accepted_source_marks
#print axioms successful_fixture
end AspisR1.Uni_SecondMarks
end
