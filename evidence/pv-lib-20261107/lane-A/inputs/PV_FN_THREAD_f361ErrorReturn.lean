import PV_FN_THREAD_ReturnWithTail
import PV_THR2_IntrinsicAtContinuation
import PV_THR2_F361
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f361ErrorReturn
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
def source : Site := match PV_THR2_F361.node219 with
  | .leaf (.ret site _) => site | _ => ⟨0,0,.null⟩
def cost {W : Type} (_B : Carrier W Data) (c : Config) (_w : W) :=
  1 + PV_THR2_IntrinsicFrameReturnCall.extra c.store c.frame.activation c.callers
def finish {W E : Type} (B : Carrier W Data) (c : Config) (w : W) (es : List E) (stack : List Config) :=
  PV_FN_THREAD_ReturnWithTail.after B c.store c.frame.activation c.callers c.frame.loops
    source (PV_THR2_F361.live.body.drop 145) w es stack
def steps {W E : Type} (B : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  PV_THR2_IntrinsicAtContinuation.steps (PV_THR2_F361.block220.drop 39 ++ PV_THR2_F361.live.body.drop 145) (cost B) q
def after {W E : Type} (B : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  PV_THR2_IntrinsicAtContinuation.after (PV_THR2_F361.block220.drop 39 ++ PV_THR2_F361.live.body.drop 145) (finish B) q
theorem run {W E : Type} (B : Carrier W Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data) (q : PV_THR2_IntrinsicState.State W E) :
    PV_THR2_IntrinsicState.advance B K P H (steps B q) q = after B q := by
  apply PV_THR2_IntrinsicAtContinuation.run
  intro c w es stack h
  rcases c with ⟨⟨a,rest,loops,wait,unwind,done⟩,parents,s⟩
  rcases h with ⟨rfl,rfl,rfl,rfl⟩
  change PV_THR2_IntrinsicState.advance B K P H
    (1 + PV_THR2_IntrinsicFrameReturnCall.extra s a parents)
    ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F361.node219 :: PV_THR2_F361.live.body.drop 145,loops := loops},parents,s⟩,w,es⟩,stack⟩ = _
  exact PV_FN_THREAD_ReturnWithTail.run B K P H s a parents loops source _ w es stack
#print axioms run
end PV_FN_THREAD_f361ErrorReturn
