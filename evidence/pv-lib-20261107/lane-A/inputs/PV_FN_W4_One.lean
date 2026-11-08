import PV_THR2_IntrinsicAtContinuation
import PV_THR2_IntrinsicCompatible
set_option autoImplicit false
noncomputable section
namespace PV_FN_W4_One
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
/-- One named source instruction. Its actual Execution outcome is retained;
this does not select a successful dynamic operand, match, Drop, abort or loop. -/
def finish {W E : Type} (C : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (c : Config) (w : W) (es : List E) (stack : List Config) : PV_THR2_IntrinsicState.State W E :=
  let p := PV_THR2_Execution.step C ctl programs H c w
  ⟨⟨p.status,p.world,es ++ p.events⟩,stack⟩

def steps {W E : Type} (nodes : List PV_STX2_SliceSyntax.Node) (q : PV_THR2_IntrinsicState.State W E) :=
  PV_THR2_IntrinsicAtContinuation.steps nodes (fun _ _ => 1) q

def after {W E : Type} (C : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (nodes : List PV_STX2_SliceSyntax.Node) (q : PV_THR2_IntrinsicState.State W E) :=
  PV_THR2_IntrinsicAtContinuation.after nodes (finish C ctl programs H) q

/-- No callee body is executed: Ready excludes pending/completed requests, so
this is exactly one instruction of the current row, or zero on other outcomes. -/
theorem run {W E : Type} (C : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (nodes : List PV_STX2_SliceSyntax.Node) (q : PV_THR2_IntrinsicState.State W E) :
    PV_THR2_IntrinsicState.advance C ctl programs H (steps nodes q) q = after C ctl programs H nodes q := by
  apply PV_THR2_IntrinsicAtContinuation.run
  intro c w es stack h
  change PV_THR2_IntrinsicState.advance C ctl programs H 1 ⟨⟨.running c,w,es⟩,stack⟩ = _
  simp only [PV_THR2_IntrinsicState.advance]
  exact PV_THR2_IntrinsicCompatible.step C ctl programs H c w es stack
    (PV_THR2_IntrinsicCompatible.not_waiting c h.2.1)
#print axioms run
end PV_FN_W4_One
