import NDO_JFo_QueryStage
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFo_ScalarStage
open Aeneas Aeneas.Std Result AspisR1Stage2

theorem source : T2Nat_ScalarStage.body (CheckpointBytes4Ops.ops true)
    JFx_NativeBytes.checkpoint .S2 10#u8 1736#usize JFq_State.value JFq_Root0.value JFq_Root1.value
    (JFq_Raw.reader 176#usize)=ok (.Ok (JFo_Prepared.value,JFo_Prepared.accumulator)) := by
  have step0 := JFq_Gamma.source
  have step1 := JFq_Kappa.source
  have step2 := JFq_Alpha0.source
  have step3 := JFq_Alpha1.source
  have step4 := JFq_Rho.source
  simp only [T2Nat_ScalarStage.body,CheckpointBytes4Ops.ops,T2Nat_Try.withRead,
    step0,step1,step2,step3,step4,
    bind_tc_ok,Aeneas.Std.uncurry]
  exact JFo_QueryStage.source

#print axioms source
end AspisR1.JFo_ScalarStage
end
