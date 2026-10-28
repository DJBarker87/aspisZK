import RPv_FIv_SubMap
import RPu_FIq_Native14
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIv_EqualityCell
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode K)
abbrev call := FIq_Native.pool_v1.pair_forest_semantic_terminal.equality_value.closure.Insts.CoreOpsFunctionFnPairQM31QM31QM31.call

theorem value (a b out : NQ) (ha : Canon a) (hb : Canon b)
    (run : call () (a,b)=ok out) :
    Canon out ∧ decode out=decode a*decode b+(1-decode a)*(1-decode b) := by
  unfold call FIq_Native.pool_v1.pair_forest_semantic_terminal.equality_value.closure.Insts.CoreOpsFunctionFnPairQM31QM31QM31.call at run
  obtain ⟨ab,hab,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨q,hq,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨q1,hq1,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨q2,hq2,run⟩ := FIv_Map.bind_success _ _ _ run
  have vab := FIv_NativeValue.mul a b ab ha hb hab
  have vq := FIv_SubMap.qm FIq_Native.field.QM31.ONE a q FIv_NativeValue.one.1 ha hq
  have vq1 := FIv_SubMap.qm q b q1 vq.1 hb hq1
  have vq2 := FIv_NativeValue.add q1 ab q2 vq1.1 vab.1 hq2
  have vout := FIv_NativeValue.add q2 ab out vq2.1 vab.1 run
  refine ⟨vout.1,?_⟩
  rw [vout.2,vq2.2,vq1.2,vq.2,vab.2,FIv_NativeValue.one.2]
  ring

#print axioms value
end AspisR1.FIv_EqualityCell
end
