import NFG_QueryLoopReplay
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFG_QueryLoopSource
open Aeneas Aeneas.Std Result AspisR1Stage2 NFG_QueryLoopDefs
/-- The actual emitted loop on every typed initial state. Only a root fuel
bound remains; child progress follows from the body, including raw failures. -/
theorem complete (ops : Port3_NativeQueryBody.Ops) (proof : Slice U8)
 (p : verifier.Prepared) (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (geometry : verifier.QueryGeometry) (finish : Usize) (fuel : Nat) (state : State)
 (budget : Budget finish fuel state) :
 run (fun a b => Port3_NativeQueryBody.verifier.candidate.query_values ops proof p a g none geometry b)
  finish fuel state = Port3_NativeQueryBody.verifier.candidate.query_loop_loop
  ops state proof p g none geometry finish := by
 let query : Query := fun a b => Port3_NativeQueryBody.verifier.candidate.query_values ops proof p a g none geometry b
 have body : step query finish=Port3_NativeQueryBody.verifier.candidate.query_loop_loop.body
    ops proof p g none geometry finish := funext (step_source ops proof p g geometry finish)
 change run query finish fuel state = loop
  (Port3_NativeQueryBody.verifier.candidate.query_loop_loop.body ops proof p g none geometry finish) state
 rw [←body]
 exact NFG_QueryLoopReplay.complete query (source_progress ops proof p g geometry) finish fuel state budget
#print axioms complete
end AspisR1.NFG_QueryLoopSource
end
