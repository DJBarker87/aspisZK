import PV_THR2_IntrinsicChildCall
import PV_THR2_IntrinsicFrameOrdinary
import PV_THR2_IntrinsicAtContinuation
import PV_THR2_Source270Table
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f361ErrorCall280
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
def source : Site × Data × Data × List Operand × Nat := match PV_THR2_F361.node182 with
  | .leaf (.call site (.object [("Regular",.object [("kind",kind),("generics",generics)])]) args (.local dest) []) => (site,kind,generics,args,dest)
  | _ => (⟨0,0,.null⟩,.null,.null,[],0)
def fn : Data := match PV_THR2_F361.node182 with
  | .leaf (.call _ f _ _ _) => f | _ => .null
def cost {W : Type} (base : Carrier W Data) (c : Config) (w : W) :=
  PV_THR2_IntrinsicChildCall.steps base c.store c.frame.activation source.2.2.2.1 w
def finish {W E : Type} (base : Carrier W Data) (handler : PV_STX2_Native.Request Data → W → Reply W E Data) (c : Config) (w : W) (es : List E) (stack : List Config) :=
  PV_THR2_IntrinsicChildCall.after base handler c.store c.frame.activation c.callers c.frame.loops
    ((PV_THR2_F361.block220.drop 5 ++ PV_THR2_F361.live.body.drop 145)) source.1 fn source.2.2.2.1 source.2.2.2.2 w es stack
noncomputable def steps {W E : Type} (base : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  PV_THR2_IntrinsicAtContinuation.steps ((PV_THR2_F361.block220.drop 4 ++ PV_THR2_F361.live.body.drop 145)) (cost base) q
noncomputable def after {W E : Type} (base : Carrier W Data) (handler : PV_STX2_Native.Request Data → W → Reply W E Data) (q : PV_THR2_IntrinsicState.State W E) :=
  PV_THR2_IntrinsicAtContinuation.after ((PV_THR2_F361.block220.drop 4 ++ PV_THR2_F361.live.body.drop 145)) (finish base handler) q
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (q : PV_THR2_IntrinsicState.State W E) (child : programs fn = none) :
    PV_THR2_IntrinsicState.advance base ctl
      programs handler (steps base q) q = after base handler q := by
  apply PV_THR2_IntrinsicAtContinuation.run
  intro c w es stack h
  rcases c with ⟨⟨a,rest,loops,wait,unwind,done⟩,parents,s⟩
  rcases h with ⟨rfl,rfl,rfl,rfl⟩
  change PV_THR2_IntrinsicState.advance base ctl _ handler (PV_THR2_IntrinsicChildCall.steps base s a source.2.2.2.1 w)
    ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F361.node182 :: (PV_THR2_F361.block220.drop 5 ++ PV_THR2_F361.live.body.drop 145),loops := loops},parents,s⟩,w,es⟩,stack⟩ = _
  exact PV_THR2_IntrinsicChildCall.run base ctl _ handler s a parents loops _ source.1 source.2.1 source.2.2.1 source.2.2.2.1 source.2.2.2.2 w es stack (by rfl) (by
    intro t vs
    apply PV_THR2_IntrinsicFrameOrdinary.run
    intro heq
    have ids := congrArg PV_THR2_OffPath.functionId heq
    cases ids) child
#print axioms run
end PV_FN_THREAD_f361ErrorCall280
