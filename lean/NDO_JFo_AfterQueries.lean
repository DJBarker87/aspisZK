import NDO_JFo_Suffix
import NDO_JFq_QueryValidation
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFo_AfterQueries
open Aeneas Aeneas.Std Result AspisR1Stage2

theorem source : T2Nat_AfterQueries.normalized (CheckpointBytes4Ops.ops true)
    JFx_NativeBytes.checkpoint .S2 10#u8 1736#usize JFq_State.value JFq_Root0.value JFq_Root1.value
    JFq_Gamma.scalar JFq_Kappa.scalar JFq_Alpha0.scalar JFq_Alpha1.scalar JFq_Rho.scalar
    JFq_Queries.value (JFq_Raw.reader 408#usize)=
      ok (.Ok (JFo_Prepared.value,JFo_Prepared.accumulator)) := by
  have semantic : CheckpointBytes4Ops.readSemanticAlpha JFx_NativeBytes.checkpoint
      (JFq_Raw.reader 408#usize).at=ok (.Ok (JFq_Semantic.value,568#usize)) := JFq_Semantic.source
  simp only [T2Nat_AfterQueries.normalized,T2Nat_Try.withOk,
    CheckpointBytes4Ops.ops,JFq_QueryValidation.source,semantic,
    bind_tc_ok,Aeneas.Std.uncurry]
  exact JFo_Suffix.source

#print axioms source
end AspisR1.JFo_AfterQueries
end
