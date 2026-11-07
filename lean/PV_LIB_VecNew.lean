import PV_LIB_Observation
import PV_FN_THREAD_f164
set_option autoImplicit false
noncomputable section
namespace PV_LIB_VecNew
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine

/-- The CLOSED root's all-answer deterministic function, literally. -/
abbrev internalModel := @PV_FN_THREAD_f164.output

def law {W E : Type} (base : Carrier W Data) (b : Bool)
    (s : Store Data) (a dest : Nat) (parent : Frame) (parents : List Frame)
    (r : Reply W E Data) (es : List E) (stack : List Config)
    (out : PV_LIB.MachineObservation W E) : Prop :=
  out = PV_LIB.observe (internalModel base b s a dest parent parents r es stack)

theorem installed {W E : Type} (base : Carrier W Data) (ctl : Control)
    (fallback : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a dest : Nat) (parent : Frame) (parents : List Frame)
    (wait : PV_STX2_Native.Waiting Data) (b : Bool) (w : W) (es : List E) (stack : List Config)
    (pre : PV_FN_THREAD_f164.Pre s a dest parent parents wait) :
    law base b s a dest parent parents (PV_FN_THREAD_f164.reply handler s w) es stack
      (PV_LIB.observe (PV_THR2_IntrinsicState.advance (PV_FN_THREAD_f164.carrier base b) ctl
        (PV_THR2_Source208Table.table (PV_THR2_Source15Table.resolve
          (PV_THR2_OwnInitChildren.resolve fallback))) handler
        (4 + PV_THR2_Source164Continue268.steps (PV_FN_THREAD_f164.reply handler s w))
        ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F164.live.body},parent :: parents,s⟩,
          w,es⟩,stack⟩)) :=
  congrArg PV_LIB.observe (PV_FN_THREAD_f164.contract base ctl fallback handler s a dest parent parents wait
    b w es stack pre).1

#print axioms installed
end PV_LIB_VecNew
