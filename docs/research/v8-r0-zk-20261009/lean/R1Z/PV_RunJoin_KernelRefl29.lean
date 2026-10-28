import R1Z.PV_RunJoin_HeadControl29
open Lean Meta Elab Tactic
namespace R1Z.PV_RunJoin_KernelRefl29

/-- Construct the ordinary Eq.refl term at the left side of an equality.
This avoids elaborator conversion of long factored control expressions;
the kernel must still check conversion against the declared theorem type.
It introduces no constant, equality premise, axiom or limit override. -/
elab "pv_kernel_refl" : tactic => do
  let goal ← getMainGoal
  let proof ← withMainContext do
    let ty ← instantiateMVars (← goal.getType)
    unless ty.isAppOfArity ``Eq 3 do throwError "expected equality"
    mkEqRefl ty.getAppArgs[1]!
  goal.assign proof
  replaceMainGoal []

theorem smoke (n : Nat) : (let k := n+1; k+1) = n+1+1 := by
  pv_kernel_refl
#print axioms smoke
end R1Z.PV_RunJoin_KernelRefl29
