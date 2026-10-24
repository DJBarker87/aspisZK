import Port17RELEASE_Domain
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port17RELEASE_TX1
open Aeneas Aeneas.Std Result VTop_Stages VTop_Trace VTop_OracleCode
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open Port15DRIVER_Local Port15DRIVER_Cost Port17RELEASE_Domain
theorem tx1 (ops : Ops) (reserved : Bool) (unwrap : Port6CK_Semantic.Unwrap)
    (rest : Implementation) (w : Nat → Nat) (budgets : ReleaseBudgets rest w)
    {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (semantic : Port1_Driver.Semantic) (pub proof : Slice U8) (H : Bytes → AspisV8R19.SourceDuplexStep.State) :
    Fits (Port9OR_Installed.implementation ops reserved unwrap rest) H
      (VTop_Flow.tx1 VTop_Flow.traceEffects D semantic pub proof 10#usize hash none) (Port15DRIVER_TX1.sites w) := by
  unfold Port15DRIVER_TX1.sites
  repeat' first
    | control_node
    | (apply Port15DRIVER_Local.library; simp [operationId, delegatedIds, VTop_OracleStages.libraryIds])
    | (refine Nat.le_trans (Port17RELEASE_Domain.delegated ops reserved unwrap rest w budgets _ _ ?_ ?_) ?_
       · simp [operationId, delegatedIds]; done
       · first | exact True.intro | exact rfl
       · exact Nat.le_refl _)
    | exact Port12COUNT_Installed.batch0 _ _ _ _ _ _
    | exact Port11PROV_SourceCount.writer_count _ _ _ _ _ _ _
    | (intro)
  all_goals first
    | exact Port17RELEASE_Domain.delegated ops reserved unwrap rest w budgets _ _ (by simp [operationId, delegatedIds]) (by simp [ReleaseCall])
    | exact Port17RELEASE_Domain.delegated ops reserved unwrap rest w budgets (.op12 .S2) H (by simp [operationId, delegatedIds]) (by simp [ReleaseCall])



#print axioms tx1
end AspisR1.Port17RELEASE_TX1
end
