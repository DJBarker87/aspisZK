import XRn_Join_Funs
open Aeneas Aeneas.Std Result ControlFlow
open XRn_Join_Release
set_option autoImplicit false
namespace XRr_QueryStop
/-- An already rejected query state issues no suffix query. -/
theorem rejected {H : Type} (proof : Slice U8) (p : verifier.Prepared)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (obs : Option (verifier.Phase → Result Unit)) (geo : verifier.QueryGeometry)
 (end1 : Usize) (e : verifier.Error) :
 verifier.candidate.query_loop_loop (.Err e) proof p g obs geo end1=ok (.Err e) := by
 unfold verifier.candidate.query_loop_loop
 rw [Aeneas.Std.loop.eq_def]
 rfl
/-- A stopped accepted state retains the SAME accumulator and pending rows. -/
theorem stopped (proof : Slice U8) (p : verifier.Prepared) (a : verifier.Accumulator)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (obs : Option (verifier.Phase → Result Unit)) (geo : verifier.QueryGeometry)
 (b : verifier.BatchedWeights) (end1 : Usize) (h : end1.val ≤ a.next.val) :
 verifier.candidate.query_loop proof p a g obs geo b end1=ok (.Ok (a,b)) := by
 unfold verifier.candidate.query_loop verifier.candidate.query_loop_loop
 rw [Aeneas.Std.loop.eq_def]
 simp [verifier.candidate.query_loop_loop.body,h]
#print axioms rejected
#print axioms stopped
end XRr_QueryStop
