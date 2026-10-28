import NDO_JFo_AfterQueries
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFo_QueryStage
open Aeneas Aeneas.Std Result AspisR1Stage2

theorem source : T2Nat_QuerySource.normalized (CheckpointBytes4Ops.ops true)
    JFx_NativeBytes.checkpoint .S2 10#u8 1736#usize JFq_State.value JFq_Root0.value JFq_Root1.value
    JFq_Gamma.scalar JFq_Kappa.scalar JFq_Alpha0.scalar JFq_Alpha1.scalar JFq_Rho.scalar
    (JFq_Raw.reader 320#usize)=ok (.Ok (JFo_Prepared.value,JFo_Prepared.accumulator)) := by
  simp only [T2Nat_QuerySource.normalized,CheckpointBytes4Ops.ops,JFq_Queries.source,
    bind_tc_ok,Aeneas.Std.uncurry]
  exact JFo_AfterQueries.source

#print axioms source
end AspisR1.JFo_QueryStage
end
