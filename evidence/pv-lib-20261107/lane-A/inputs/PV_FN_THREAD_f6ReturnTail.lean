import PV_FN_THREAD_f6LoopBack
import PV_THR2_SourceReturn
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f6ReturnTail
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine

def prepared (t : Store Data) (a : Nat) :=
  write (write (write (write (write (write (write (write (write (write (write t
    ⟨a,2,[]⟩ none) ⟨a,39,[]⟩ none) ⟨a,38,[]⟩ none) ⟨a,37,[]⟩ none)
    ⟨a,36,[]⟩ none) ⟨a,35,[]⟩ none) ⟨a,33,[]⟩ none) ⟨a,26,[]⟩ none)
    ⟨a,25,[]⟩ none) ⟨a,24,[]⟩ none) ⟨a,1,[]⟩ none

/-- Eleven own storage deaths after the actual Scope drop. The incoming store
is that drop's Post store. No drop implementation or guessed frame is used. -/
theorem run {W E : Type} (B : Carrier W Data) (ctl : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (t : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (rest : List PV_STX2_SliceSyntax.Node) (w : W) (es : List E) (stack : List Config) :
    PV_THR2_IntrinsicState.advance B ctl P H 11
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.block157.drop 16 ++ rest,loops := loops},parents,t⟩,w,es⟩,stack⟩ =
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.node156 :: rest,loops := loops},parents,prepared t a⟩,w,es⟩,stack⟩ := by
  have shape : PV_THR2_F6.block157.drop 16 =
    [PV_THR2_F6.node145,PV_THR2_F6.node146,PV_THR2_F6.node147,PV_THR2_F6.node148,
      PV_THR2_F6.node149,PV_THR2_F6.node150,PV_THR2_F6.node151,PV_THR2_F6.node152,
      PV_THR2_F6.node153,PV_THR2_F6.node154,PV_THR2_F6.node155,PV_THR2_F6.node156] := rfl
  rw [shape]
  simp [PV_THR2_IntrinsicState.advance,PV_THR2_IntrinsicState.step,PV_THR2_Catch316Segment.select,
    PV_THR2_Execution.step,PV_THR2_Dynamic.active,PV_THR2_Dynamic.operandOf,
    PV_THR2_GapCompletion.step,PV_THR2_AggregateCompletion.complete,
    PV_THR2_AggregateCompletion.carrier,PV_STX2_SliceMachine.step,
    PV_THR2_F6.node145,PV_THR2_F6.node146,PV_THR2_F6.node147,PV_THR2_F6.node148,
    PV_THR2_F6.node149,PV_THR2_F6.node150,PV_THR2_F6.node151,PV_THR2_F6.node152,
    PV_THR2_F6.node153,PV_THR2_F6.node154,PV_THR2_F6.node155,
    native,adopt,PV_STX2_Native.step,PV_STX2_Store.bind,write,prepared]

theorem frame (t : Store Data) (a : Nat) (q : Address) (outside : q.activation ≠ a) :
    (prepared t a).cells q = t.cells q := by
  have neq (i : Nat) : q ≠ (⟨a,i,[]⟩ : Address) := by
    intro eq
    exact outside (congrArg Address.activation eq)
  simp [prepared,write,neq]

theorem return_cell (t : Store Data) (a : Nat) :
    (prepared t a).cells ⟨a,0,[]⟩ = t.cells ⟨a,0,[]⟩ := by simp [prepared,write]

#print axioms run
#print axioms frame
#print axioms return_cell
end PV_FN_THREAD_f6ReturnTail
