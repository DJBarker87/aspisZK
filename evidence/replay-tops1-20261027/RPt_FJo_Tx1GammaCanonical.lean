import RPt_FJo_Tx1Scratch
import F3L_WriterNumeric
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJo_Tx1GammaCanonical
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller InstalledPreparation
/-- Canonicality for the writer's actual gamma, derived from TX1 preparation. -/
theorem value {CoreError H : Type} (ops : Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops CoreError)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (D : aspis_core.digest.Digest32 H) (hash : H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (publicBytes proof : Slice U8) (split : Usize) (saved : alloc.vec.Vec U8)
    (run : Tx1Q_Execution.Run (Tx1Q_Execution.actual ops reserved query geo B std)
      reserved query geo D hash pub publicBytes proof split saved) :
    OraclePortCkptAbi4Decode.CanonicalWide
      (CheckpointBytes3Namespaces.toE (Tx1Q_Carriers.prepared run.p).gamma) := by
  obtain ⟨p,rs,output,scratch,h,cells⟩ := FJo_Tx1Scratch.value ops reserved query geo B std D hash pub publicBytes proof split saved run
  rw [←output]
  exact ⟨⟨h.1.1.1,h.1.1.2,h.1.2.1,h.1.2.2⟩,⟨h.2.1.1,h.2.1.2,h.2.2.1,h.2.2.2⟩⟩
#print axioms value
end AspisR1.FJo_Tx1GammaCanonical
end
