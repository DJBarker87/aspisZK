import RPu_FIo_MixedValues
import RPu_FJc_LowModel
import RPu_FJf_QMArray
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJg_ScalarCell
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open FIo_FieldBridge (NQ NE wide qm)
abbrev C := FIo_Native.weights.Weights.scalar_factor.closure

def term (p : Array NE 4#usize) (f : Array NQ 4#usize) (s : Nat) : AspisWideTower.WideExact :=
  FIp_ArrayValue.value p (FJc_LowModel.perm s)*
    algebraMap OraclePortCheckpointAbiC5.K OraclePortCheckpointAbiC5.E (FJf_QMArray.value f s)

def sumPrefix (p : Array NE 4#usize) (f : Array NQ 4#usize) : Nat → AspisWideTower.WideExact
  | 0 => 0
  | n+1 => sumPrefix p f n+term p f n

theorem value (p : Array NE 4#usize) (f : Array NQ 4#usize)
    (hp : FIo_ArrayCanon.Holds p) (v out : NE) (hv : FIo_WideValues.Canon v)
    (s : Usize) (next : C)
    (run : FIo_Native.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact.call_mut
      (p,f) (v,s)=ok (out,next)) :
    next=(p,f) ∧ FIo_WideValues.Canon out ∧
    decodeWide (wide out)=decodeWide (wide v)+term p f s.val := by
  unfold FIo_Native.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact.call_mut at run
  obtain ⟨i,hi,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨pv,hpv,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨fv,hfv,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨product,hproduct,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨sum,hsum,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases Result.ok.inj run
  have cp := FIo_ArrayCanon.read p i pv hp hpv
  have vp := FIo_MixedValues.mul_qm pv product fv cp hproduct
  have vs := FIo_WideValues.add v product out hv vp.1 hsum
  refine ⟨rfl,vs.1,?_⟩
  rw [vs.2,vp.2,term,FJc_LowModel.perm_read s i hi,
    FIp_ArrayValue.read p i pv hpv,FJf_QMArray.read f s fv hfv]
#print axioms value
end AspisR1.FJg_ScalarCell
end
