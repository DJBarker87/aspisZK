import Port15DRIVER_Local
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port15DRIVER_TX1
open Aeneas Aeneas.Std Result VTop_Stages VTop_Trace VTop_OracleCode
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open Port15DRIVER_Local Port15DRIVER_Cost

open Lean Elab Tactic Meta
elab "control_node" : tactic => do
  let target ← getMainTarget
  unless target.isAppOf ``Fits do throwError "not a source tree"
  let args := target.getAppArgs
  let tree ← whnf args[3]!
  let goal ← (← getMainGoal).change (mkAppN target.getAppFn (args.set! 3 tree))
  replaceMainGoal [goal]
  match tree.getAppFn.constName? with
  | some ``Code.done => evalTactic (← `(tactic| apply Port15DRIVER_Cost.done))
  | some ``Code.step => evalTactic (← `(tactic| apply Port15DRIVER_Cost.step))
  | some ``Code.call => evalTactic (← `(tactic| apply Port15DRIVER_Cost.call))
  | _ => evalTactic (← `(tactic| split))

def sites (w : Nat → Nat) : List Nat :=
  [0,w 3,w 4,0,0,w 7,w 12,0,0,0,0,477,0,w 11,w 10,w 6,w 9,3,0]

theorem tx1 (ops : Ops) (reserved : Bool) (unwrap : Port6CK_Semantic.Unwrap)
    (rest : Implementation) (w : Nat → Nat) (budgets : LocalBudgets rest w)
    {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (semantic : Port1_Driver.Semantic) (pub proof : Slice U8) (H : Bytes → AspisV8R19.SourceDuplexStep.State) :
    Fits (Port9OR_Installed.implementation ops reserved unwrap rest) H
      (VTop_Flow.tx1 VTop_Flow.traceEffects D semantic pub proof 10#usize hash none) (sites w) := by
  unfold sites
  repeat' first
    | control_node
    | (apply Port15DRIVER_Local.library; decide)
    | (apply Port15DRIVER_Local.delegated ops reserved unwrap rest w budgets; decide)
    | exact Port12COUNT_Installed.batch0 _ _ _ _ _ _
    | exact Port11PROV_SourceCount.writer_count _ _ _ _ _ _ _
    | (intro)
  all_goals control_node

#print axioms tx1
end AspisR1.Port15DRIVER_TX1
end
