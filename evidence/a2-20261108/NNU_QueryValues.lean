import NNU_QueryAccum
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNU_QueryValues
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeQueryBody NNH_Run5bQuerySlots

theorem callback (g h : Ops) (decode : g.op21=h.op21) :
 verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact g =
 verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact h := by
 have hm : verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut g =
  verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut h := by
  funext c i
  simp only [verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut,decode]
 have ho : verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeWideExact.call_once g =
  verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeWideExact.call_once h := by
  funext c i
  simp only [verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeWideExact.call_once,hm]
 unfold verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact
 unfold verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeWideExact
 rw [hm,ho]

theorem source (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)
 (proof : Slice U8) (p : verifier.Prepared) (a : verifier.Accumulator)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize) (geo : verifier.QueryGeometry)
 (pending : verifier.BatchedWeights) (hq : NBF_PowerStep.Canonical a.power) :
 verifier.candidate.query_values (actual m env err r) proof p a g none geo pending =
 verifier.candidate.query_values model proof p a g none geo pending := by
 have s:=NNU_QueryAccum.slots m env err r
 have h0 : @(actual m env err r).op0 = @model.op0 := by rfl
 have h11 : (actual m env err r).op11 = model.op11 := by rfl
 have h16 := funext (fun x=>funext (fun y=>funext (NNH_Run5bQuerySlots.line m env err r x y)))
 have h17 := funext (fun x=>funext (fun y=>funext (NNH_Run5bQuerySlots.circle m env err r x y)))
 have h18 := funext (fun x=>funext (NNH_Run5bQuerySlots.geometry m env err r x))
 have h20 := funext (fun x=>funext (NNH_Run5bQuerySlots.dots m env err r x))
 have h21 := funext (fun x=>funext (NNH_Run5bQuerySlots.decode m env err r x))
 have hEq : (actual m env err r).widePartialEq = model.widePartialEq := by rfl
 have phase : ∀ ph, (actual m env err r).op19 none ph = model.op19 none ph := by intro ph; rfl
 unfold verifier.candidate.query_values
 simp only [h11,h20,s.trace,h18,h17,h0,callback _ _ h21,hEq,h16,s.mul,s.double,s.one,s.sub,
  NNU_QueryAccum.source m env err r p a _ _ pending hq,phase]
#print axioms callback
#print axioms source
end AspisR1.NNU_QueryValues
end
