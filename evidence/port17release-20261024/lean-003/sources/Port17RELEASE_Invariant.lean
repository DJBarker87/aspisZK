import Port17RELEASE_Domain
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port17RELEASE_Invariant
open Aeneas Aeneas.Std Result VTop_Stages VTop_Trace VTop_OracleCode
open Port17RELEASE_Domain
open Lean Elab Tactic Meta
elab "release_node" : tactic => withMainContext do
  try evalTactic (← `(tactic| dsimp only [VTop_Trace.bind])) catch _ => pure ()
  try evalTactic (← `(tactic| split))
  catch _ =>
    let target ← getMainTarget
    unless target.isAppOf ``CallsIn do throwError "not a source-domain goal"
    let args := target.getAppArgs
    let tree ← whnf args[1]!
    let goal ← (← getMainGoal).change (mkAppN target.getAppFn (args.set! 1 tree))
    replaceMainGoal [goal]
    evalTactic (← `(tactic| simp only [CallsIn]))

theorem tx1 {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (semantic : Port1_Driver.Semantic) (pub proof : Slice U8) :
    CallsIn (VTop_Flow.tx1 VTop_Flow.traceEffects D semantic pub proof 10#usize hash none) := by
  repeat' first
    | (exact True.intro)
    | (constructor)
    | (intro)
    | (simp only [ReleaseCall]; exact rfl)
    | release_node

theorem tx2 {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (pub proof checkpoint : Slice U8) :
    CallsIn (VTop_Flow.tx2_authenticated VTop_Flow.traceEffects D pub proof checkpoint hash none) := by
  repeat' first
    | (exact True.intro)
    | (constructor)
    | (intro)
    | (simp only [ReleaseCall]; exact rfl)
    | release_node

#print axioms tx1
#print axioms tx2
end AspisR1.Port17RELEASE_Invariant
end
