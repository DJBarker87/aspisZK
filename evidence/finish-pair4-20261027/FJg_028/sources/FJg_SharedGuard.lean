import FJg_NativeShared
import FJg_GuardEquality
import FJc_InstalledParts
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJg_SharedGuard
open Aeneas Aeneas.Std Result
open AspisR1Stage2 AspisR1Stage2.Stage2Finish

theorem result (alpha : Array K 10#usize)
    (z : Array aspis_core.circle.SecureCirclePoint 2#usize) (w : FIo_Install.W)
    (hw : FIn_WeightsInstall.newWeights .S2 alpha z=ok (.Ok w))
    (b : Bool) (run : FIo_Native.weights.shared_two_point_guard (FIo_Install.toWeights w) 2#usize=ok b) :
    b=true := by
  obtain ⟨points,a8,a9,f1,f2,hp,h8,h9,hf1,hf2,hvariant,rest⟩ := FJc_InstalledParts.value .S2 alpha z w hw
  unfold FIo_Native.weights.shared_two_point_guard at run
  simp only [hvariant,FIo_Install.variant,FIn_WeightsInstall.variant,
    FIo_Native.transport.Variant.Insts.CoreCmpPartialEqVariant.eq,
    decide_true,bind_tc_ok,ite_true] at run
  obtain ⟨row0,h0,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨digit02,h02,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨row2,h2,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨digit22,h22,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  have eq2 := FJg_NativeShared.reads .S2 alpha z w hw 2#usize (Or.inl rfl)
    row0 row2 digit02 digit22 h0 h2 h02 h22
  rw [←eq2,FJg_GuardEquality.array,bind_tc_ok,if_pos rfl] at run
  obtain ⟨digit03,h03,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨digit23,h23,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  have eq3 := FJg_NativeShared.reads .S2 alpha z w hw 3#usize (Or.inr rfl)
    row0 row2 digit03 digit23 h0 h2 h03 h23
  rw [←eq3,FJg_GuardEquality.array] at run
  exact (Result.ok.inj run).symm
#print axioms result
end AspisR1.FJg_SharedGuard
end
