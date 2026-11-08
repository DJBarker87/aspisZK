import PV_THR2_IntrinsicFramePlaceMatch
import PV_THR2_IntrinsicAtContinuation
import PV_THR2_F361
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f361Match144
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
def source : Site × Place × List (List Nat × List PV_STX2_SliceSyntax.Node) × Option (List PV_STX2_SliceSyntax.Node) := match PV_THR2_F361.node221 with
  | .matchAdt site place arms otherwise => (site,place,arms,otherwise)
  | _ => (⟨0,0,.null⟩,.local 0,[],none)
def finish {W E : Type} (base : Carrier W Data) (ctl : Control) (c : Config) (w : W) (es : List E) (stack : List Config) : PV_THR2_IntrinsicState.State W E :=
  ⟨⟨PV_THR2_IntrinsicFramePlaceMatch.result base ctl c.store c.frame.activation c.callers c.frame.loops
    (PV_THR2_F361.live.body.drop 145) source.1 source.2.1 source.2.2.1 source.2.2.2 w,w,es⟩,stack⟩
noncomputable def steps {W E : Type} (_base : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  PV_THR2_IntrinsicAtContinuation.steps (PV_THR2_F361.live.body.drop 144) (fun _ _ => 1) q
noncomputable def after {W E : Type} (base : Carrier W Data) (ctl : Control) (q : PV_THR2_IntrinsicState.State W E) :=
  PV_THR2_IntrinsicAtContinuation.after (PV_THR2_F361.live.body.drop 144) (finish base ctl) q
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (q : PV_THR2_IntrinsicState.State W E) :
    PV_THR2_IntrinsicState.advance base ctl programs handler (steps base q) q = after base ctl q := by
  apply PV_THR2_IntrinsicAtContinuation.run
  intro c w es stack h
  rcases c with ⟨⟨a,rest,loops,wait,unwind,done⟩,parents,s⟩
  rcases h with ⟨rfl,rfl,rfl,rfl⟩
  change PV_THR2_IntrinsicState.advance base ctl programs handler 1
    ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F361.node221 :: PV_THR2_F361.live.body.drop 145,loops := loops},parents,s⟩,w,es⟩,stack⟩ = _
  exact PV_THR2_IntrinsicFramePlaceMatch.run base ctl programs handler s a parents loops _ source.1 source.2.1 source.2.2.1 source.2.2.2 w es stack
#print axioms run
end PV_FN_THREAD_f361Match144
namespace PV_FN_THREAD_f361Match149
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
def source : Site × Place × List (List Nat × List PV_STX2_SliceSyntax.Node) × Option (List PV_STX2_SliceSyntax.Node) := match PV_THR2_F361.node228 with
  | .matchAdt site place arms otherwise => (site,place,arms,otherwise)
  | _ => (⟨0,0,.null⟩,.local 0,[],none)
def finish {W E : Type} (base : Carrier W Data) (ctl : Control) (c : Config) (w : W) (es : List E) (stack : List Config) : PV_THR2_IntrinsicState.State W E :=
  ⟨⟨PV_THR2_IntrinsicFramePlaceMatch.result base ctl c.store c.frame.activation c.callers c.frame.loops
    (PV_THR2_F361.live.body.drop 150) source.1 source.2.1 source.2.2.1 source.2.2.2 w,w,es⟩,stack⟩
noncomputable def steps {W E : Type} (_base : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  PV_THR2_IntrinsicAtContinuation.steps (PV_THR2_F361.live.body.drop 149) (fun _ _ => 1) q
noncomputable def after {W E : Type} (base : Carrier W Data) (ctl : Control) (q : PV_THR2_IntrinsicState.State W E) :=
  PV_THR2_IntrinsicAtContinuation.after (PV_THR2_F361.live.body.drop 149) (finish base ctl) q
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (q : PV_THR2_IntrinsicState.State W E) :
    PV_THR2_IntrinsicState.advance base ctl programs handler (steps base q) q = after base ctl q := by
  apply PV_THR2_IntrinsicAtContinuation.run
  intro c w es stack h
  rcases c with ⟨⟨a,rest,loops,wait,unwind,done⟩,parents,s⟩
  rcases h with ⟨rfl,rfl,rfl,rfl⟩
  change PV_THR2_IntrinsicState.advance base ctl programs handler 1
    ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F361.node228 :: PV_THR2_F361.live.body.drop 150,loops := loops},parents,s⟩,w,es⟩,stack⟩ = _
  exact PV_THR2_IntrinsicFramePlaceMatch.run base ctl programs handler s a parents loops _ source.1 source.2.1 source.2.2.1 source.2.2.2 w es stack
#print axioms run
end PV_FN_THREAD_f361Match149
