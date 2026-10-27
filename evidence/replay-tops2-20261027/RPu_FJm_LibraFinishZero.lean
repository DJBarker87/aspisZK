import RPu_FJm_WriteOrder
import RPu_FJm_LibraStages
import RPu_FJc_ArrayUpdateValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJm_LibraFinishZero
open Aeneas Aeneas.Std Result ControlFlow AspisR1CurrentWide.Proof
open FIo_FieldBridge (NE NQ wide qm)
attribute [local irreducible] QuadraticAlgebra.instInv

theorem value (low first2 first3 all : NE) (i3 : Usize) (q4 q16 : NQ)
    (ap1 before out : Array NE 4#usize) (cursor cursorOut : FIo_RangeNext.Range)
    (cl : FIo_WideValues.Canon low) (c3 : FIo_WideValues.Canon first3) (ca : FIo_WideValues.Canon all)
    (cb : FIo_ArrayCanon.Holds before)
    (run : FJm_LibraStages.finish 0#usize low i3 first2 first3 all q4 q16 ap1 before cursor=
      ok (.cont (cursorOut,out))) :
    cursorOut=cursor ∧ FIo_ArrayCanon.Holds out ∧ ∀ j,FIp_ArrayValue.value out j=
      if j=0 then decodeWide (wide low)*decodeWide (wide all)
      else if j=1 then decodeWide (wide low)*decodeWide (wide first3)*
        algebraMap OraclePortCheckpointAbiC5.K OraclePortCheckpointAbiC5.E (decodeQM (qm q16))
      else FIp_ArrayValue.value before j := by
  unfold FJm_LibraStages.finish at run
  simp only [ite_true] at run
  obtain ⟨v0,hv0,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨mid,hmid,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨v1,hv1,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨v16,hv16,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨last,hlast,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases Result.ok.inj run
  have p0 := FIo_WideMulValues.mul low all v0 cl ca hv0
  have p1 := FIo_WideMulValues.mul low first3 v1 cl c3 hv1
  have p16 := FIo_MixedValues.mul_qm v1 v16 q16 p1.1 hv16
  have cmid := FIo_ArrayCanon.update before mid 0#usize v0 cb p0.1 hmid
  refine ⟨rfl,FIo_ArrayCanon.update mid out 1#usize v16 cmid p16.1 hlast,?_⟩
  intro j
  rw [FJc_ArrayUpdateValue.value mid out 1#usize v16 j hlast,
    FJc_ArrayUpdateValue.value before mid 0#usize v0 j hmid,p0.2,p16.2,p1.2]
  simp only [show (0#usize).val=0 from by decide,show (1#usize).val=1 from by decide]
  exact FJm_WriteOrder.two _ _ _ j
#print axioms value
end AspisR1.FJm_LibraFinishZero
end
