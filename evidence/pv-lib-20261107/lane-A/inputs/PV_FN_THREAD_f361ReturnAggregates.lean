import PV_THR2_IntrinsicFrameAggregate
import PV_THR2_IntrinsicAtContinuation
import PV_THR2_F361
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f361Aggregate155
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
def source : Site × Place × Data × List Operand := match PV_THR2_F361.node234 with
  | .leaf (.aggregateMove site dest kind captures) => (site,dest,kind,captures)
  | _ => (⟨0,0,.null⟩,.local 0,.null,[])
def finish {W E : Type} (base : Carrier W Data) (c : Config) (w : W) (es : List E) (stack : List Config) :=
  PV_THR2_IntrinsicFrameAggregate.after base c.store c.frame.activation c.callers c.frame.loops
    (PV_THR2_F361.live.body.drop 156) source.1 source.2.1 source.2.2.1 source.2.2.2 w es stack
noncomputable def steps {W E : Type} (_base : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  PV_THR2_IntrinsicAtContinuation.steps (PV_THR2_F361.live.body.drop 155) (fun _ _ => 1) q
noncomputable def after {W E : Type} (base : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  PV_THR2_IntrinsicAtContinuation.after (PV_THR2_F361.live.body.drop 155) (finish base) q
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (q : PV_THR2_IntrinsicState.State W E) :
    PV_THR2_IntrinsicState.advance base ctl programs handler (steps base q) q = after base q := by
  apply PV_THR2_IntrinsicAtContinuation.run
  intro c w es stack h
  rcases c with ⟨⟨a,rest,loops,wait,unwind,done⟩,parents,s⟩
  rcases h with ⟨rfl,rfl,rfl,rfl⟩
  change PV_THR2_IntrinsicState.advance base ctl programs handler 1
    ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F361.node234 :: PV_THR2_F361.live.body.drop 156,loops := loops},parents,s⟩,w,es⟩,stack⟩ = _
  exact PV_THR2_IntrinsicFrameAggregate.run base ctl programs handler s a parents loops _ source.1 source.2.1 source.2.2.1 source.2.2.2 w es stack
#print axioms run
end PV_FN_THREAD_f361Aggregate155
namespace PV_FN_THREAD_f361Aggregate159
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
def source : Site × Place × Data × List Operand := match PV_THR2_F361.node238 with
  | .leaf (.aggregateMove site dest kind captures) => (site,dest,kind,captures)
  | _ => (⟨0,0,.null⟩,.local 0,.null,[])
def finish {W E : Type} (base : Carrier W Data) (c : Config) (w : W) (es : List E) (stack : List Config) :=
  PV_THR2_IntrinsicFrameAggregate.after base c.store c.frame.activation c.callers c.frame.loops
    (PV_THR2_F361.live.body.drop 160) source.1 source.2.1 source.2.2.1 source.2.2.2 w es stack
noncomputable def steps {W E : Type} (_base : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  PV_THR2_IntrinsicAtContinuation.steps (PV_THR2_F361.live.body.drop 159) (fun _ _ => 1) q
noncomputable def after {W E : Type} (base : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  PV_THR2_IntrinsicAtContinuation.after (PV_THR2_F361.live.body.drop 159) (finish base) q
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (q : PV_THR2_IntrinsicState.State W E) :
    PV_THR2_IntrinsicState.advance base ctl programs handler (steps base q) q = after base q := by
  apply PV_THR2_IntrinsicAtContinuation.run
  intro c w es stack h
  rcases c with ⟨⟨a,rest,loops,wait,unwind,done⟩,parents,s⟩
  rcases h with ⟨rfl,rfl,rfl,rfl⟩
  change PV_THR2_IntrinsicState.advance base ctl programs handler 1
    ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F361.node238 :: PV_THR2_F361.live.body.drop 160,loops := loops},parents,s⟩,w,es⟩,stack⟩ = _
  exact PV_THR2_IntrinsicFrameAggregate.run base ctl programs handler s a parents loops _ source.1 source.2.1 source.2.2.1 source.2.2.2 w es stack
#print axioms run
end PV_FN_THREAD_f361Aggregate159
