import FJl_CallIndex
import Port3_QueryStage
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJl_LoopExtraction
open Aeneas Aeneas.Std Result AspisR1Stage2
open Port3_NativeQueryBody
abbrev E := aspis_core.field.wide_exact.WideExact
/-- Every cursor in the successful source loop names an actual call in that loop. -/
theorem native (ops : Ops) (proof : Slice U8) (p : verifier.Prepared)
    (a out : verifier.Accumulator) (g : Array E 29#usize)
    (obs : Option (verifier.Phase → Result Unit)) (geometry : verifier.QueryGeometry)
    (b bout : verifier.BatchedWeights) (stop : Usize) (bound : a.next.val≤stop.val)
    (success : verifier.candidate.query_loop ops proof p a g obs geometry b stop=ok (.Ok (out,bout)))
    (j : Nat) (lower : a.next.val≤j) (upper : j<stop.val) :
    ∃ a0 a1 b0 b1, a0.next.val=j ∧
      verifier.candidate.query_values ops proof p a0 g obs geometry b0=ok (.Ok (a1,b1)) := by
  rw [Port3_NativeQueryFrame.loop_eq] at success
  have advance := fun a a1 b b1 h =>
    (Port3_NativeQueryFrame.query_fields ops proof p a a1 g obs geometry b b1 h).2.2
  exact FJl_CallIndex.reached _ stop.val advance a out b bout _
    (Port2_QueryLoop.source_calls _ proof p g obs geometry stop advance a out b bout bound success)
    j lower upper

theorem installed (ops : Ops) (proof : Slice U8) (p : verifier.Prepared)
    (a out : verifier.Accumulator) (g : Array E 29#usize)
    (geometry : verifier.QueryGeometry) (b bout : verifier.BatchedWeights)
    (stop : Usize) (bound : a.next.val≤stop.val)
    (success : Port3_QueryStage.query ops proof p a g none geometry b stop=ok (.Ok (out,bout)))
    (j : Nat) (lower : a.next.val≤j) (upper : j<stop.val) :
    ∃ a0 a1 b0 b1, a0.next.val=j ∧
      verifier.candidate.query_values (Port3_QueryStage.release ops) proof p a0 g none geometry b0=ok (.Ok (a1,b1)) := by
  exact native _ proof p a out g none geometry b bout stop bound
    ((Port3_QueryInstall.success_iff _ _).mp success) j lower upper
#print axioms native
#print axioms installed
end AspisR1.FJl_LoopExtraction
end
