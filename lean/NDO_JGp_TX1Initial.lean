import NDO_JGp_Prepare
import RPz7_Tx1Q_Nonvacuity
set_option autoImplicit false
namespace AspisR1.JGp_TX1Initial
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation AspisR1ClaimPreparedBridge FirstComposition

def zeroQ : aspis_core.field.QM31 := ⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩
def zero : aspis_core.field.wide_exact.WideExact := ⟨zeroQ,zeroQ⟩

theorem zeroCall {C : Type} (base : Ops) (query : Port3_NativeQueryBody.Ops)
    (geo : Port3_NativeGeometryBody.Ops C) :
    aspis_core.field.wide_exact.WideExact.ZERO (JGp_PrepareLayout.installed base query geo)=ok zero := by
  unfold aspis_core.field.wide_exact.WideExact.ZERO
  rfl
#print axioms zeroCall

theorem inhabited {C H : Type} (base : Ops) (query : Port3_NativeQueryBody.Ops)
    (geo : Port3_NativeGeometryBody.Ops C) (D : aspis_core.digest.Digest32 H) (hash : H) :
    let ops := JGp_PrepareLayout.installed (JGp_Allocation.base base) query geo
    let D0 := F3V_OracleDictionary.current JFp_SHADigest.digest D
    ∃ (p : verifier.Prepared) (scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
      (initial : verifier.Accumulator) (pending : verifier.BatchedWeights),
      verifier.candidate.prepare ops D0 (toCurrentPublic JFs_PublicSerialization.value)
        JFx_NativeBytes.proof hash none (Array.repeat 29#usize zero)=ok (.Ok p,scratch) ∧
      ops.op20 .S2=ok (.Ok initial) ∧
      ops.op18 initial.weights.deref=ok (.Ok pending) ∧
      verifier.candidate.tx1 ops D0 (toCurrentPublic JFs_PublicSerialization.value)
        JFx_NativeBytes.publicInput JFx_NativeBytes.proof 10#usize hash none=
        Tx1Reachability.afterPrepare ops D0 JFx_NativeBytes.publicInput JFx_NativeBytes.proof
          10#usize hash none p scratch := by
  dsimp only
  obtain ⟨p,scratch,prepare⟩ := JGp_Prepare.inhabited base query geo D hash (Array.repeat 29#usize zero)
  obtain ⟨initial,pending,init,pend⟩ := Tx1Q_Nonvacuity.initial_pending
  refine ⟨p,scratch,initial,pending,prepare,?_,?_,?_⟩
  · exact init
  · exact pend
  · have dispatch := JGi_TX1Dispatch.writer (JGp_Allocation.base base) query geo
      JGe_Boundaries.value (NP6_StdModel.calls (.Ok ()))
      (F3V_OracleDictionary.current JFp_SHADigest.digest D)
      (toCurrentPublic JFs_PublicSerialization.value) JFx_NativeBytes.publicInput hash
    erw [dispatch]
    unfold JGi_TX1Control.afterScan
    erw [zeroCall,bind_tc_ok,prepare,bind_tc_ok]
    rfl
#print axioms inhabited
end AspisR1.JGp_TX1Initial
