import Port15DRIVER_TX1
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port16CUT_TX2
open Aeneas Aeneas.Std Result VTop_Stages VTop_Trace VTop_OracleCode
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open Port15DRIVER_Local Port15DRIVER_Cost

def sites (w : Nat → Nat) : List Nat :=
  [w 3,0,3,0,w 17,0,0,0,0,0,0,0,0,563,0,w 11,w 10,w 6,w 9,0,0,w 19]

theorem tx2 (ops : Ops) (reserved : Bool) (unwrap : Port6CK_Semantic.Unwrap)
    (rest : Implementation) (w : Nat → Nat) (budgets : LocalBudgets rest w)
    {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (pub proof checkpoint : Slice U8) (H : Bytes → State) :
    Fits (Port9OR_Installed.implementation ops reserved unwrap rest) H
      (VTop_Flow.tx2_authenticated VTop_Flow.traceEffects D pub proof checkpoint hash none) (sites w) := by
  unfold sites
  repeat' first
    | control_node
    | (apply Port15DRIVER_Local.library; simp [operationId, VTop_OracleStages.libraryIds])
    | (refine Nat.le_trans (Port15DRIVER_Local.delegated ops reserved unwrap rest w budgets _ _ ?_) ?_
       · simp [operationId, delegatedIds]
       · exact Nat.le_refl _)
    | exact Port12COUNT_Installed.batch1 _ _ _ _ _ _
    | exact Port9OR_Budget.reader_count _ _ _ _ _ _ _ _ _
    | (intro)

#print tx2
#print sites
#print axioms tx2
end AspisR1.Port16CUT_TX2
end
