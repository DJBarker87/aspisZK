import PV_FN_THREAD_LocalDropRun
import PV_THR2_IntrinsicAtContinuation
import PV_THR2_F361
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f361ErrorDrop19
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
def source : Site × Data := match PV_THR2_F361.node199 with
  | .leaf (.drop site _ fn _ _) => (site,fn) | _ => (⟨0,0,.null⟩,.null)
def cost {W : Type} (B : Carrier W Data) (c : Config) (_w : W) :=
  PV_FN_THREAD_LocalDrop.steps B c.store c.frame.activation 17
def finish {W E : Type} (B : Carrier W Data)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (c : Config) (w : W) (es : List E) (stack : List Config) :=
  PV_FN_THREAD_LocalDrop.after B H c.store c.frame.activation 17 c.callers c.frame.loops
    (PV_THR2_F361.block220.drop 20 ++ PV_THR2_F361.live.body.drop 145) source.1 source.2 false w es stack
def steps {W E : Type} (B : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  PV_THR2_IntrinsicAtContinuation.steps (PV_THR2_F361.block220.drop 19 ++ PV_THR2_F361.live.body.drop 145) (cost B) q
def after {W E : Type} (B : Carrier W Data)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data) (q : PV_THR2_IntrinsicState.State W E) :=
  PV_THR2_IntrinsicAtContinuation.after (PV_THR2_F361.block220.drop 19 ++ PV_THR2_F361.live.body.drop 145) (finish B H) q
theorem run {W E : Type} (B : Carrier W Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data) (q : PV_THR2_IntrinsicState.State W E) :
    PV_THR2_IntrinsicState.advance B K P H (steps B q) q = after B H q := by
  apply PV_THR2_IntrinsicAtContinuation.run
  intro c w es stack h
  rcases c with ⟨⟨a,rest,loops,wait,unwind,done⟩,parents,s⟩
  rcases h with ⟨rfl,rfl,rfl,rfl⟩
  change PV_THR2_IntrinsicState.advance B K P H
    (PV_FN_THREAD_LocalDrop.steps B s a 17)
    ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F361.node199 :: (PV_THR2_F361.block220.drop 20 ++ PV_THR2_F361.live.body.drop 145),loops := loops},parents,s⟩,w,es⟩,stack⟩ = _
  exact PV_FN_THREAD_LocalDropRun.run B K P H s a 17 parents loops _ source.1 source.2 false w es stack
#print axioms run
end PV_FN_THREAD_f361ErrorDrop19
namespace PV_FN_THREAD_f361ErrorDrop23
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
def source : Site × Data := match PV_THR2_F361.node203 with
  | .leaf (.drop site _ fn _ _) => (site,fn) | _ => (⟨0,0,.null⟩,.null)
def cost {W : Type} (B : Carrier W Data) (c : Config) (_w : W) :=
  PV_FN_THREAD_LocalDrop.steps B c.store c.frame.activation 10
def finish {W E : Type} (B : Carrier W Data)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (c : Config) (w : W) (es : List E) (stack : List Config) :=
  PV_FN_THREAD_LocalDrop.after B H c.store c.frame.activation 10 c.callers c.frame.loops
    (PV_THR2_F361.block220.drop 24 ++ PV_THR2_F361.live.body.drop 145) source.1 source.2 false w es stack
def steps {W E : Type} (B : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  PV_THR2_IntrinsicAtContinuation.steps (PV_THR2_F361.block220.drop 23 ++ PV_THR2_F361.live.body.drop 145) (cost B) q
def after {W E : Type} (B : Carrier W Data)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data) (q : PV_THR2_IntrinsicState.State W E) :=
  PV_THR2_IntrinsicAtContinuation.after (PV_THR2_F361.block220.drop 23 ++ PV_THR2_F361.live.body.drop 145) (finish B H) q
theorem run {W E : Type} (B : Carrier W Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data) (q : PV_THR2_IntrinsicState.State W E) :
    PV_THR2_IntrinsicState.advance B K P H (steps B q) q = after B H q := by
  apply PV_THR2_IntrinsicAtContinuation.run
  intro c w es stack h
  rcases c with ⟨⟨a,rest,loops,wait,unwind,done⟩,parents,s⟩
  rcases h with ⟨rfl,rfl,rfl,rfl⟩
  change PV_THR2_IntrinsicState.advance B K P H
    (PV_FN_THREAD_LocalDrop.steps B s a 10)
    ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F361.node203 :: (PV_THR2_F361.block220.drop 24 ++ PV_THR2_F361.live.body.drop 145),loops := loops},parents,s⟩,w,es⟩,stack⟩ = _
  exact PV_FN_THREAD_LocalDropRun.run B K P H s a 10 parents loops _ source.1 source.2 false w es stack
#print axioms run
end PV_FN_THREAD_f361ErrorDrop23
