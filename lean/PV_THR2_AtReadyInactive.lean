import PV_THR2_FrameChainResultControl
set_option autoImplicit false
namespace PV_THR2_AtReadyInactive
open PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
/-- Symbolic control-only skip for retained segments belonging to the other arm.
Hypotheses are internal source control and different continuation lengths;
no store or child payload is reduced. Amended-translator conditional. -/
theorem after {W E : Type} (nodes target : List PV_STX2_SliceSyntax.Node)
    (finish : Config → W → List E → List Config → PV_THR2_IntrinsicState.State W E)
    (q : PV_THR2_IntrinsicState.State W E) (c : Config)
    (running : q.current.status = .running c)
    (ready : PV_THR2_IntrinsicAtContinuation.Ready target c)
    (different : nodes.length ≠ target.length) :
    PV_THR2_IntrinsicAtContinuation.after nodes finish q = q := by
  apply PV_THR2_FrameChainResultControl.inactive
  intro d status selected
  have eq : c = d := by rw [running] at status; cases status; rfl
  subst d
  exact different (congrArg List.length (selected.1.symm.trans ready.1))
#print axioms after
end PV_THR2_AtReadyInactive
