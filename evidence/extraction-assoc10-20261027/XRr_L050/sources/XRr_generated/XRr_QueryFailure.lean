import XRr_QueryStop
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XRr_QueryFailure
/-- Exact first failed query is preserved; no successful suffix is assumed. -/
theorem fail (proof : Slice U8) (p : verifier.Prepared) (a : verifier.Accumulator)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (obs : Option (verifier.Phase → Result Unit)) (geo : verifier.QueryGeometry)
 (b : verifier.BatchedWeights) (end1 : Usize) (active : a.next.val<end1.val)
 (e : Error) (h : verifier.candidate.query_values proof p a g obs geo b=.fail e) :
 verifier.candidate.query_loop proof p a g obs geo b end1=.fail e := by
 unfold verifier.candidate.query_loop verifier.candidate.query_loop_loop
 rw [Aeneas.Std.loop.eq_def]
 simp [verifier.candidate.query_loop_loop.body,h,show ¬end1.val≤a.next.val by omega]

theorem div (proof : Slice U8) (p : verifier.Prepared) (a : verifier.Accumulator)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (obs : Option (verifier.Phase → Result Unit)) (geo : verifier.QueryGeometry)
 (b : verifier.BatchedWeights) (end1 : Usize) (active : a.next.val<end1.val)
 (h : verifier.candidate.query_values proof p a g obs geo b=.div) :
 verifier.candidate.query_loop proof p a g obs geo b end1=.div := by
 unfold verifier.candidate.query_loop verifier.candidate.query_loop_loop
 rw [Aeneas.Std.loop.eq_def]
 simp [verifier.candidate.query_loop_loop.body,h,show ¬end1.val≤a.next.val by omega]

theorem rejected (proof : Slice U8) (p : verifier.Prepared) (a : verifier.Accumulator)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (obs : Option (verifier.Phase → Result Unit)) (geo : verifier.QueryGeometry)
 (b : verifier.BatchedWeights) (end1 : Usize) (active : a.next.val<end1.val)
 (e : verifier.Error) (h : verifier.candidate.query_values proof p a g obs geo b=ok (.Err e)) :
 verifier.candidate.query_loop proof p a g obs geo b end1=ok (.Err e) := by
 unfold verifier.candidate.query_loop verifier.candidate.query_loop_loop
 rw [Aeneas.Std.loop.eq_def]
 simpa [verifier.candidate.query_loop_loop.body,h,show ¬end1.val≤a.next.val by omega,
   verifier.candidate.query_loop_loop] using
   XRr_QueryStop.rejected (H:=Unit) proof p g obs geo end1 e
#print axioms fail
#print axioms div
#print axioms rejected
end XRr_QueryFailure
