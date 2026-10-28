import NDO_JGi_TX1Control
set_option autoImplicit false
namespace AspisR1.JGi_TX1Dispatch
open Aeneas Aeneas.Std Result AspisR1CurrentCaller

theorem tx1 {C H : Type} (ops : Ops) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (D : aspis_core.digest.Digest32 H) (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub : Slice U8) (hash : H) :
    verifier.candidate.tx1 (Tx1Q_Execution.actual ops true query geo B std) D semantic pub JFx_NativeBytes.proof 10#usize hash none=
      JGi_TX1Control.afterScan (Tx1Q_Execution.actual ops true query geo B std) D semantic pub JFx_NativeBytes.proof hash := by
  obtain ⟨shape,scan⟩ := JGi_TX1Prefix.tx1 ops query geo B std
  exact JGi_TX1Control.source _ _ _ _ _ _ shape scan
#print axioms tx1

theorem writer {C H : Type} (ops : Ops) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (D : aspis_core.digest.Digest32 H) (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub : Slice U8) (hash : H) :
    verifier.candidate.tx1 (WAdm_Execution.actual ops true query geo B std) D semantic pub JFx_NativeBytes.proof 10#usize hash none=
      JGi_TX1Control.afterScan (WAdm_Execution.actual ops true query geo B std) D semantic pub JFx_NativeBytes.proof hash := by
  obtain ⟨shape,scan⟩ := JGi_TX1Prefix.writer ops query geo B std
  exact JGi_TX1Control.source _ _ _ _ _ _ shape scan
#print axioms writer
end AspisR1.JGi_TX1Dispatch
