import RPu_FIr_NativeSub
import RPu_FIq_Native14
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIr_EqualityCell
open Aeneas Aeneas.Std Result
open FIr_NativeArithmetic (NQ)
open FIr_NativeValue (Canon decode K)
abbrev call := FIq_Native.pool_v1.pair_forest_semantic_terminal.equality_value.closure.Insts.CoreOpsFunctionFnPairQM31QM31QM31.call

theorem value (a b out : NQ) (ha : Canon a) (hb : Canon b)
    (run : call () (a,b)=ok out) :
    Canon out ∧ decode out=decode a*decode b+(1-decode a)*(1-decode b) := by
  unfold call FIq_Native.pool_v1.pair_forest_semantic_terminal.equality_value.closure.Insts.CoreOpsFunctionFnPairQM31QM31QM31.call at run
  obtain ⟨ab,hab,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨q,hq,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨q1,hq1,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨q2,hq2,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  have vab := FIr_NativeValue.mul a b ab ha hb hab
  have vq := FIr_NativeSub.qm FIq_Native.field.QM31.ONE a q FIr_NativeValue.one.1 ha hq
  have vq1 := FIr_NativeSub.qm q b q1 vq.1 hb hq1
  have vq2 := FIr_NativeValue.add q1 ab q2 vq1.1 vab.1 hq2
  have vout := FIr_NativeValue.add q2 ab out vq2.1 vab.1 run
  refine ⟨vout.1,?_⟩
  rw [vout.2,vq2.2,vq1.2,vq.2,vab.2,FIr_NativeValue.one.2]
  ring

#print axioms value
end AspisR1.FIr_EqualityCell
end
