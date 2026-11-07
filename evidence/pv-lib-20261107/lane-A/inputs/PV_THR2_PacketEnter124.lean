import PV_THR2_IntrinsicStructuredCall
import PV_THR2_IntrinsicFrameOrdinary
import PV_THR2_IntrinsicAtContinuation
import PV_THR2_PacketConstructionTable
set_option autoImplicit false
namespace PV_THR2_PacketEnter124
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
/-- Conditional on amended-translator acceptance. Hypotheses: none.
Thread-11: execute retained structured function124; all operand failures remain. -/
def source : Site × Data × Data × List Operand × Nat := match PV_THR2_F361.node70 with
  | .leaf (.call site (.object [("Regular",.object [("kind",kind),("generics",generics)])]) args (.local dest) []) => (site,kind,generics,args,dest)
  | _ => (⟨0,0,.null⟩,.null,.null,[],0)
/-- Conditional on amended-translator acceptance. Hypotheses: none.
Thread-11: execute retained structured function124; all operand failures remain. -/
def cost {W : Type} (base : Carrier W Data) (c : Config) (w : W) :=
  PV_THR2_IntrinsicStructuredCall.steps base c.store c.frame.activation source.2.2.2.1 w
/-- Conditional on amended-translator acceptance. Hypotheses: none.
Thread-11: execute retained structured function124; all operand failures remain. -/
def finish {W E : Type} (base : Carrier W Data) (c : Config) (w : W) (es : List E) (stack : List Config) :=
  PV_THR2_IntrinsicStructuredCall.after base c.store c.frame.activation c.callers c.frame.loops
    (PV_THR2_F361.live.body.drop 59) source.1 PV_THR2_Source361PacketChildren.fn58 source.2.2.2.1 source.2.2.2.2 PV_THR2_F124.live w es stack
/-- Conditional on amended-translator acceptance. Hypotheses: none.
Thread-11: execute retained structured function124; all operand failures remain. -/
noncomputable def steps {W E : Type} (base : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  PV_THR2_IntrinsicAtContinuation.steps (PV_THR2_F361.live.body.drop 58) (cost base) q
/-- Conditional on amended-translator acceptance. Hypotheses: none.
Thread-11: execute retained structured function124; all operand failures remain. -/
noncomputable def after {W E : Type} (base : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  PV_THR2_IntrinsicAtContinuation.after (PV_THR2_F361.live.body.drop 58) (finish base) q
/-- Conditional on amended-translator acceptance. Hypotheses: none.
Thread-11: execute retained structured function124; all operand failures remain. -/
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (fallback : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (q : PV_THR2_IntrinsicState.State W E) :
    PV_THR2_IntrinsicState.advance base ctl
      (PV_THR2_PacketConstructionTable.resolve fallback) handler (steps base q) q = after base q := by
  apply PV_THR2_IntrinsicAtContinuation.run
  intro c w es stack h
  rcases c with ⟨⟨a,rest,loops,wait,unwind,done⟩,parents,s⟩
  rcases h with ⟨rfl,rfl,rfl,rfl⟩
  change PV_THR2_IntrinsicState.advance base ctl _ handler (PV_THR2_IntrinsicStructuredCall.steps base s a [.move (.local 18)] w)
    ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F361.node70 :: PV_THR2_F361.live.body.drop 59,loops := loops},parents,s⟩,w,es⟩,stack⟩ = _
  exact PV_THR2_IntrinsicStructuredCall.run base ctl _ handler s a parents loops _ source.1 source.2.1 source.2.2.1 source.2.2.2.1 source.2.2.2.2 PV_THR2_F124.live w es stack (by rfl) (by
    intro t vs
    apply PV_THR2_IntrinsicFrameOrdinary.run
    intro heq
    have ids := congrArg PV_THR2_OffPath.functionId heq
    cases ids) (PV_THR2_PacketConstructionTable.at124 fallback)
#print axioms run
end PV_THR2_PacketEnter124
