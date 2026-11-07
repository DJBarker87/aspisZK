import PV_THR2_Source361Full63
import PV_THR2_Source361Full70
set_option autoImplicit false
namespace PV_THR2_PacketMetadataChildRuns
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
/-- Retained exact child segment under any resolver that selects this named
child. Resolution is an internal table fact, never an endpoint premise. -/
theorem at63 {W E : Type} (base : Carrier W Data) (ctl : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (q : PV_THR2_IntrinsicState.State W E)
    (child : P PV_THR2_Source361PacketChildren.fn63 = none) :
    PV_THR2_IntrinsicState.advance base ctl
      P handler (PV_THR2_Source361Full63.steps base q) q = PV_THR2_Source361Full63.after base handler q := by
  apply PV_THR2_IntrinsicAtContinuation.run
  intro c w es stack h
  rcases c with ⟨⟨a,rest,loops,wait,unwind,done⟩,parents,s⟩
  rcases h with ⟨rfl,rfl,rfl,rfl⟩
  change PV_THR2_IntrinsicState.advance base ctl _ handler (PV_THR2_IntrinsicChildCall.steps base s a PV_THR2_Source361Full63.source.2.2.2.1 w)
    ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F361.node75 :: PV_THR2_F361.live.body.drop 64,loops := loops},parents,s⟩,w,es⟩,stack⟩ = _
  exact PV_THR2_IntrinsicChildCall.run base ctl _ handler s a parents loops _ PV_THR2_Source361Full63.source.1 PV_THR2_Source361Full63.source.2.1 PV_THR2_Source361Full63.source.2.2.1 PV_THR2_Source361Full63.source.2.2.2.1 PV_THR2_Source361Full63.source.2.2.2.2 w es stack (by rfl) (by
    intro t vs
    apply PV_THR2_IntrinsicFrameOrdinary.run
    intro heq
    have ids := congrArg PV_THR2_OffPath.functionId heq
    cases ids) child
#print axioms at63
/-- Retained exact child segment under any resolver that selects this named
child. Resolution is an internal table fact, never an endpoint premise. -/
theorem at70 {W E : Type} (base : Carrier W Data) (ctl : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (q : PV_THR2_IntrinsicState.State W E)
    (child : P PV_THR2_Source361PacketChildren.fn70 = none) :
    PV_THR2_IntrinsicState.advance base ctl
      P handler (PV_THR2_Source361Full70.steps base q) q = PV_THR2_Source361Full70.after base handler q := by
  apply PV_THR2_IntrinsicAtContinuation.run
  intro c w es stack h
  rcases c with ⟨⟨a,rest,loops,wait,unwind,done⟩,parents,s⟩
  rcases h with ⟨rfl,rfl,rfl,rfl⟩
  change PV_THR2_IntrinsicState.advance base ctl _ handler (PV_THR2_IntrinsicChildCall.steps base s a PV_THR2_Source361Full70.source.2.2.2.1 w)
    ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F361.node82 :: PV_THR2_F361.live.body.drop 71,loops := loops},parents,s⟩,w,es⟩,stack⟩ = _
  exact PV_THR2_IntrinsicChildCall.run base ctl _ handler s a parents loops _ PV_THR2_Source361Full70.source.1 PV_THR2_Source361Full70.source.2.1 PV_THR2_Source361Full70.source.2.2.1 PV_THR2_Source361Full70.source.2.2.2.1 PV_THR2_Source361Full70.source.2.2.2.2 w es stack (by rfl) (by
    intro t vs
    apply PV_THR2_IntrinsicFrameOrdinary.run
    intro heq
    have ids := congrArg PV_THR2_OffPath.functionId heq
    cases ids) child
#print axioms at70
end PV_THR2_PacketMetadataChildRuns
