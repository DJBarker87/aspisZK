import RPu_FJm_WriteOrder
import RPu_FJm_LibraStages
import RPu_FJc_ArrayUpdateValue
import RPu_FJg_Quarter
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJm_LibraFinishOne
open Aeneas Aeneas.Std Result ControlFlow AspisR1CurrentWide.Proof
open FIo_FieldBridge (NE NQ wide qm)
attribute [local irreducible] QuadraticAlgebra.instInv

theorem value (low first2 first3 all : NE) (i3 : Usize) (q4 q16 : NQ)
    (ap1 before out : Array NE 4#usize) (cursor cursorOut : FIo_RangeNext.Range)
    (cl : FIo_WideValues.Canon low) (c2 : FIo_WideValues.Canon first2) (ca : FIo_WideValues.Canon all)
    (cp : FIo_ArrayCanon.Holds ap1) (cb : FIo_ArrayCanon.Holds before)
    (cq4 : FIo_QMValues.Canon q4) (cq16 : FIo_QMValues.Canon q16)
    (run : FJm_LibraStages.finish 1#usize low i3 first2 first3 all q4 q16 ap1 before cursor=
      ok (.cont (cursorOut,out))) :
    cursorOut=cursor ∧ FIo_ArrayCanon.Holds out ∧ ∀ j,FIp_ArrayValue.value out j=
      if j=1 then FIp_ArrayValue.value before 1+decodeWide (wide low)*
        (RoundPairing.quarter*FIp_ArrayValue.value ap1 i3.val)
      else if j=2 then decodeWide (wide low)*decodeWide (wide all)*
        algebraMap OraclePortCheckpointAbiC5.K OraclePortCheckpointAbiC5.E (decodeQM (qm q4))
      else if j=3 then decodeWide (wide low)*decodeWide (wide first2)*
        algebraMap OraclePortCheckpointAbiC5.K OraclePortCheckpointAbiC5.E
          (decodeQM (qm q16)*decodeQM (qm q4))
      else FIp_ArrayValue.value before j := by
  unfold FJm_LibraStages.finish at run
  simp only [show ¬(1#usize=0#usize) from by decide,ite_false] at run
  obtain ⟨old1,h_old1,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨p,h_p,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨scaled,h_scaled,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨lscaled,h_lscaled,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨added,h_added,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨mid1,h_mid1,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨la,h_la,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨laq,h_laq,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨mid2,h_mid2,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨l2,h_l2,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨q20,h_q20,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨l2q,h_l2q,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨last,h_last,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases Result.ok.inj run
  have co := FIo_ArrayCanon.read before 1#usize old1 cb h_old1
  have vp := FIo_ArrayCanon.read ap1 i3 p cp h_p
  have vs := FGm_WideScaleValue.value p scaled FIo_Native.weights.QUARTER h_scaled
  have vls := FIo_WideMulValues.mul low scaled lscaled cl vs.1 h_lscaled
  have vad := FIo_WideValues.add old1 lscaled added co vls.1 h_added
  have cm1 := FIo_ArrayCanon.update before mid1 1#usize added cb vad.1 h_mid1
  have vla := FIo_WideMulValues.mul low all la cl ca h_la
  have vlaq := FIo_MixedValues.mul_qm la laq q4 vla.1 h_laq
  have cm2 := FIo_ArrayCanon.update mid1 mid2 2#usize laq cm1 vlaq.1 h_mid2
  have vl2 := FIo_WideMulValues.mul low first2 l2 cl c2 h_l2
  have vq20 := FIo_QMMulValues.mul q16 q4 q20 cq16 cq4 h_q20
  have vl2q := FIo_MixedValues.mul_qm l2 l2q q20 vl2.1 h_l2q
  refine ⟨rfl,FIo_ArrayCanon.update mid2 out 3#usize l2q cm2 vl2q.1 h_last,?_⟩
  intro j
  rw [FJc_ArrayUpdateValue.value mid2 out 3#usize l2q j h_last,
    FJc_ArrayUpdateValue.value mid1 mid2 2#usize laq j h_mid2,
    FJc_ArrayUpdateValue.value before mid1 1#usize added j h_mid1,
    vad.2,vls.2,vs.2,FJg_Quarter.value,vlaq.2,vla.2,vl2q.2,vl2.2,vq20.2]
  have oldValue := FIp_ArrayValue.read before 1#usize old1 h_old1
  simp only [show (1#usize).val=1 from by decide] at oldValue
  rw [←oldValue,←FIp_ArrayValue.read ap1 i3 p h_p]
  simp only [show (1#usize).val=1 from by decide,show (2#usize).val=2 from by decide,
    show (3#usize).val=3 from by decide]
  exact FJm_WriteOrder.three _ _ _ _ j
#print axioms value
end AspisR1.FJm_LibraFinishOne
end
