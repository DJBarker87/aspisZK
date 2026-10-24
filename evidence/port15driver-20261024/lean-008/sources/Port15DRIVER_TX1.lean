import Port15DRIVER_Local
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port15DRIVER_TX1
open Aeneas Aeneas.Std Result VTop_Stages VTop_Trace VTop_OracleCode
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open Port15DRIVER_Local Port15DRIVER_Cost

macro "partition_control" ops:ident reserved:ident unwrap:ident rest:ident w:ident budgets:ident : tactic =>
  `(tactic|
    first
    | apply Port15DRIVER_Cost.done
    | (apply Port15DRIVER_Cost.step
       intro b
       dsimp only [VTop_Trace.bind]
       partition_control $ops $reserved $unwrap $rest $w $budgets)
    | (apply Port15DRIVER_Cost.call
       · first
         | (apply Port15DRIVER_Local.library; decide)
         | (apply Port15DRIVER_Local.delegated $ops $reserved $unwrap $rest $w $budgets; decide)
         | exact Port12COUNT_Installed.batch0 _ _ _ _ _ _
         | exact Port11PROV_SourceCount.writer_count _ _ _ _ _ _ _
       · intro b
         dsimp only [VTop_Trace.bind]
         partition_control $ops $reserved $unwrap $rest $w $budgets)
    | (split <;> partition_control $ops $reserved $unwrap $rest $w $budgets))

def sites (w : Nat → Nat) : List Nat :=
  [0,w 3,w 4,0,0,w 7,w 12,0,0,0,0,477,0,w 11,w 10,w 6,w 9,3,0]

theorem tx1 (ops : Ops) (reserved : Bool) (unwrap : Port6CK_Semantic.Unwrap)
    (rest : Implementation) (w : Nat → Nat) (budgets : LocalBudgets rest w)
    {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (semantic : Port1_Driver.Semantic) (pub proof : Slice U8) (H : Bytes → State) :
    Fits (Port9OR_Installed.implementation ops reserved unwrap rest) H
      (VTop_Flow.tx1 VTop_Flow.traceEffects D semantic pub proof 10#usize hash none) (sites w) := by
  unfold sites
  partition_control ops reserved unwrap rest w budgets

#print axioms tx1
end AspisR1.Port15DRIVER_TX1
end
