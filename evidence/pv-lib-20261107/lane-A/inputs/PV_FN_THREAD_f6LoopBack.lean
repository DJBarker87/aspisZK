import PV_FN_THREAD_f6CounterTest
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f6LoopBack
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine

def prepared (t : Store Data) (a : Nat) :=
  write (write (write (write t ⟨a,22,[]⟩ none) ⟨a,21,[]⟩ none)
    ⟨a,20,[]⟩ none) ⟨a,14,[]⟩ none

/-- Five OWN source instructions after128 Post: four local deaths and the
actual continue2410. The loop body's saved syntax, arbitrary lower caller
stack, world and observations are retained. No bound or termination premise. -/
theorem run {W E : Type} (B : Carrier W Data) (ctl : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (t : Store Data) (a : Nat) (parents : List Frame)
    (loop : LoopFrame) (lower : List LoopFrame)
    (w : W) (es : List E) (stack : List Config) :
    PV_THR2_IntrinsicState.advance B ctl P H 5
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.block86.drop 27,loops := loop :: lower},parents,t⟩,w,es⟩,stack⟩ =
      ⟨⟨.running ⟨{activation := a,remaining := loop.body,loops := loop :: lower},parents,prepared t a⟩,w,es⟩,stack⟩ := by
  have shape : PV_THR2_F6.block86.drop 27 =
    [PV_THR2_F6.node81,PV_THR2_F6.node82,PV_THR2_F6.node83,PV_THR2_F6.node84,PV_THR2_F6.node85] := rfl
  rw [shape]
  simp [PV_THR2_IntrinsicState.advance,PV_THR2_IntrinsicState.step,PV_THR2_Catch316Segment.select,
    PV_THR2_Execution.step,PV_THR2_Dynamic.active,PV_THR2_Dynamic.operandOf,
    PV_THR2_GapCompletion.step,PV_THR2_AggregateCompletion.complete,
    PV_STX2_SliceMachine.step,PV_THR2_F6.node81,PV_THR2_F6.node82,PV_THR2_F6.node83,
    PV_THR2_F6.node84,PV_THR2_F6.node85,native,adopt,PV_STX2_Native.step,
    PV_STX2_Store.bind,evaluate,operands,operand,PV_STX2_Store.read,
    locate,writeAddress,write,prepared]

theorem frame (t : Store Data) (a : Nat) (q : Address) (outside : q.activation ≠ a) :
    (prepared t a).cells q = t.cells q := by
  have neq (i : Nat) : q ≠ (⟨a,i,[]⟩ : Address) := by
    intro eq
    exact outside (congrArg Address.activation eq)
  simp [prepared,write,neq]

#print axioms run
#print axioms frame
end PV_FN_THREAD_f6LoopBack
