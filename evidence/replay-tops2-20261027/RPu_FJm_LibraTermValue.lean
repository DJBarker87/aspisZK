import RPu_FJm_LibraStages
import RPu_FJc_LowModel
import RPu_FJf_QMArray
import RPu_FJg_Quarter
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJm_LibraTermValue
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open FIo_FieldBridge (NQ NE qm wide)
attribute [local irreducible] QuadraticAlgebra.instInv

theorem value (ap1 : Array NE 4#usize) (high : Array NQ 4#usize) (j i : Usize) (out : NE)
    (hc : FIo_ArrayCanon.Holds ap1) (run : FJm_LibraStages.term ap1 high j=ok (i,out)) :
    i.val=FJc_LowModel.perm j.val ∧ FIo_WideValues.Canon out ∧
      decodeWide (wide out)=RoundPairing.quarter*
        (FIp_ArrayValue.value ap1 (FJc_LowModel.perm j.val)*
          algebraMap OraclePortCheckpointAbiC5.K OraclePortCheckpointAbiC5.E (FJf_QMArray.value high j.val)) := by
  unfold FJm_LibraStages.term at run
  obtain ⟨idx,hidx,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨we,hwe,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨q,hq,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨product,hproduct,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨term,hterm,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases Result.ok.inj run
  have cwe := FIo_ArrayCanon.read ap1 i we hc hwe
  have vproduct := FIo_MixedValues.mul_qm we product q cwe hproduct
  have vterm := FGm_WideScaleValue.value product out FIo_Native.weights.QUARTER hterm
  have perm := FJc_LowModel.perm_read j i hidx
  refine ⟨perm.symm,vterm.1,?_⟩
  rw [vterm.2,FJg_Quarter.value,vproduct.2,perm,
    FIp_ArrayValue.read ap1 i we hwe,FJf_QMArray.read high j q hq]
#print axioms value
end AspisR1.FJm_LibraTermValue
end
