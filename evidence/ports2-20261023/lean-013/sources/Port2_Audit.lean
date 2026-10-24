import Port2_QueryLoop
import VTop_Checkpoint
import S2LeadInterface

/-! Focused compatible-import and axiom audit, with the two concrete ranges.
This is not a coherent frozen release replay or a frozen2 identity theorem. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port2_Audit
open Aeneas Aeneas.Std Result AspisR1Stage2 Port2_QueryLoop

theorem ten_calls (aops : AccumulateOps) (ops : QueryOps) (proof : Slice U8)
    (p : verifier.Prepared) (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (geometry : verifier.QueryGeometry) (a out : Acc) (b bout : BW)
    (start : a.next.val = 0)
    (success : verifier.candidate.query_loop (verifier.candidate.queryWithOps aops ops)
      proof p a g none geometry b 10#usize = ok (.Ok (out,bout))) :
    Calls (fun a b => verifier.candidate.queryWithOps aops ops proof p a g none geometry b)
      10 a b out bout 10 ∧ out.next.val = 10 := by
  have calls := query_body_calls aops ops proof p g none geometry 10#usize a out b bout
    (by simpa [start]) success
  have fixed : Calls (fun a b => verifier.candidate.queryWithOps aops ops proof p a g none geometry b)
      10 a b out bout 10 := by simpa only [start,Nat.sub_zero] using calls
  exact ⟨fixed,returned_next _ _ _ _ _ _ _ fixed⟩

theorem twelve_calls (aops : AccumulateOps) (ops : QueryOps) (proof : Slice U8)
    (p : verifier.Prepared) (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (geometry : verifier.QueryGeometry) (a out : Acc) (b bout : BW)
    (start : a.next.val = 10)
    (success : verifier.candidate.query_loop (verifier.candidate.queryWithOps aops ops)
      proof p a g none geometry b 22#usize = ok (.Ok (out,bout))) :
    Calls (fun a b => verifier.candidate.queryWithOps aops ops proof p a g none geometry b)
      22 a b out bout 12 ∧ out.next.val = 22 := by
  have calls := query_body_calls aops ops proof p g none geometry 22#usize a out b bout
    (by simpa [start]) success
  have fixed : Calls (fun a b => verifier.candidate.queryWithOps aops ops proof p a g none geometry b)
      22 a b out bout 12 := by simpa only [start] using calls
  exact ⟨fixed,returned_next _ _ _ _ _ _ _ fixed⟩

#print axioms ten_calls
#print axioms twelve_calls
#print axioms Port2_Initial.newS2_success
#print axioms Port2_Initial.newS2_allocation
#print axioms Port2_Initial.initial_eq
#print axioms Port2_Initial.returned_initial
#print axioms Port2_ReturnedState.writer_returned
#print axioms Port2_ReturnedState.finish_prefix
#print axioms accumulate_next
#print axioms query_next
#print axioms Port2_QueryLoop.error_stops
#print axioms Port2_QueryLoop.source_calls
#print axioms Port2_QueryLoop.query_body_calls
#print axioms Port2_QueryLoop.returned_next
#print CheckpointBytes5Join.success_conditioned_checkpoint_stage_join
#print VTop_Checkpoint.CheckpointSourceJoin
end AspisR1.Port2_Audit
end
