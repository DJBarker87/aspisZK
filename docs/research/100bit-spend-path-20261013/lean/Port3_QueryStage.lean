import Port3_NativeQueryFrame

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port3_QueryStage
open Aeneas Aeneas.Std Result AspisR1Stage2

def mark (obs : Option (verifier.Phase → Result Unit)) (phase : verifier.Phase) : Result Unit :=
  match obs with | none => ok () | some f => f phase

def release (ops : Port3_NativeQueryBody.Ops) : Port3_NativeQueryBody.Ops :=
  {ops with op15 := fun _ _ _ => ok (), op19 := mark}

def query (ops : Port3_NativeQueryBody.Ops) (proof : Slice U8) (p : VTop_Stages.verifier.Prepared)
    (a : VTop_Stages.verifier.Accumulator)
    (g : Array VTop_Stages.aspis_core.field.wide_exact.WideExact 29#usize)
    (obs : Option (VTop_Stages.verifier.Phase → Result Unit)) (geometry : VTop_Stages.verifier.QueryGeometry)
    (pending : VTop_Stages.verifier.BatchedWeights) (end1 : Usize) :=
  Port3_QueryInstall.result (Port3_NativeQueryBody.verifier.candidate.query_loop (release ops)
    proof p a g (Port3_QueryInstall.observer obs) geometry pending end1)

def installed (base : VTop_Stages.Ops) (ops : Port3_NativeQueryBody.Ops) : VTop_Stages.Ops :=
  {base with op6 := query ops}

theorem loop_fields (ops : Port3_NativeQueryBody.Ops)
    (proof : Slice U8) (p : verifier.Prepared) (a out : verifier.Accumulator)
    (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (obs : Option (VTop_Stages.verifier.Phase → Result Unit)) (geometry : verifier.QueryGeometry)
    (b bout : verifier.BatchedWeights) (end1 : Usize) (bound : a.next.val≤end1.val)
    (accepted : query ops proof p a g obs geometry b end1=ok (.Ok (out,bout))) :
    out.weights=a.weights ∧ out.next.val=end1.val := by
  have native := (Port3_QueryInstall.success_iff _ _).mp accepted
  rw [Port3_NativeQueryFrame.loop_eq] at native
  have calls := Port2_QueryLoop.source_calls (Port3_NativeQueryBody.verifier.candidate.query_values (release ops))
    proof p g (Port3_QueryInstall.observer obs) geometry end1
    (fun a a1 b b1 h => (Port3_NativeQueryFrame.query_fields (release ops) proof p a a1 g
      (Port3_QueryInstall.observer obs) geometry b b1 h).2.2) a out b bout bound native
  exact ⟨Port3_QueryFrame.calls_weights _ _ _ _ _ _ _
    (fun a a1 b b1 h => (Port3_NativeQueryFrame.query_fields (release ops) proof p a a1 g
      (Port3_QueryInstall.observer obs) geometry b b1 h).2.1) calls,
    Port2_QueryLoop.returned_next _ _ _ _ _ _ _ calls⟩

theorem mark_none (phase : verifier.Phase) : mark none phase=ok () := rfl

theorem ten (ops : Port3_NativeQueryBody.Ops) (proof : Slice U8) (p : verifier.Prepared)
    (a out : verifier.Accumulator) (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (geometry : verifier.QueryGeometry) (b bout : verifier.BatchedWeights) (start : a.next.val=0)
    (accepted : query ops proof p a g none geometry b 10#usize=ok (.Ok (out,bout))) :
    out.weights=a.weights ∧ out.next.val=10 :=
  loop_fields ops proof p a out g none geometry b bout 10#usize (by rw [start]; decide) accepted

theorem twelve (ops : Port3_NativeQueryBody.Ops) (proof : Slice U8) (p : verifier.Prepared)
    (a out : verifier.Accumulator) (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (geometry : verifier.QueryGeometry) (b bout : verifier.BatchedWeights) (start : a.next.val=10)
    (accepted : query ops proof p a g none geometry b 22#usize=ok (.Ok (out,bout))) :
    out.weights=a.weights ∧ out.next.val=22 :=
  loop_fields ops proof p a out g none geometry b bout 22#usize (by rw [start]; decide) accepted

#print axioms loop_fields
#print axioms mark_none
#print axioms ten
#print axioms twelve
end AspisR1.Port3_QueryStage
end
