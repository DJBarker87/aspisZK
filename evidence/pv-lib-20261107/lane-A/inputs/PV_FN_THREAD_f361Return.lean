import PV_THR2_IntrinsicFrameReturnCall
import PV_THR2_IntrinsicAtContinuation
import PV_THR2_F361
set_option autoImplicit false
namespace PV_FN_THREAD_f361Return
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Source box reconstruction retains every missing binding and full reply case. -/
def site : Site := match PV_THR2_F361.node266 with
  | .leaf (.ret site _) => site | _ => ⟨0,0,.null⟩
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Source box reconstruction retains every missing binding and full reply case. -/
def cost (c : Config) : Nat := 1 + PV_THR2_IntrinsicFrameReturnCall.extra c.store c.frame.activation c.callers
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Source box reconstruction retains every missing binding and full reply case. -/
def finish {W E : Type} (base : Carrier W Data) (c : Config) (w : W) (es : List E) (stack : List Config) : PV_THR2_IntrinsicState.State W E :=
  PV_THR2_IntrinsicFrameReturnCall.after base c.store c.frame.activation c.callers c.frame.loops site w es stack
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Source box reconstruction retains every missing binding and full reply case. -/
noncomputable def steps {W E : Type} (_base : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  PV_THR2_IntrinsicAtContinuation.steps (PV_THR2_F361.live.body.drop 187) (fun c _ => cost c) q
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Source box reconstruction retains every missing binding and full reply case. -/
noncomputable def after {W E : Type} (base : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  PV_THR2_IntrinsicAtContinuation.after (PV_THR2_F361.live.body.drop 187) (finish base) q
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Source box reconstruction retains every missing binding and full reply case. -/
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (q : PV_THR2_IntrinsicState.State W E) :
    PV_THR2_IntrinsicState.advance base ctl programs handler (steps base q) q = after base q := by
  apply PV_THR2_IntrinsicAtContinuation.run
  intro c w es stack h
  rcases c with ⟨⟨a,rest,loops,wait,unwind,done⟩,parents,s⟩
  rcases h with ⟨rfl,rfl,rfl,rfl⟩
  change PV_THR2_IntrinsicState.advance base ctl programs handler
    (1 + PV_THR2_IntrinsicFrameReturnCall.extra s a parents)
    ⟨⟨.running ⟨{activation := a,remaining := [.leaf (.ret site (.local 0))],loops := loops},parents,s⟩,w,es⟩,stack⟩ = _
  exact PV_THR2_IntrinsicFrameReturnCall.run base ctl programs handler s a parents loops site w es stack
#print axioms run
end PV_FN_THREAD_f361Return
