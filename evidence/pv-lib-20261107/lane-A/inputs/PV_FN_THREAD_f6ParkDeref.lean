import PV_FN_THREAD_f6CounterTest
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f6ParkDeref
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine

/-- Exact emitted call descriptor at f6 node77; each126 instance is separate. -/
def fn : Data := match PV_THR2_F6.node77 with
  | .leaf (.call _ f _ _ _) => f | _ => .null

def scopeRef (a : Nat) := PV_STX2_TypedReferences.reference ⟨a,2,[0]⟩ .null
/-- Only f6's own local writes, on the preceding callee's explicit Post store. -/
def prepared (t : Store Data) (a : Nat) :=
  write (write (write (write (write (write (write (t) ⟨a,17,[]⟩ none) ⟨a,15,[]⟩ none) ⟨a,20,[]⟩ none) ⟨a,21,[]⟩ none) ⟨a,22,[]⟩ none) ⟨a,23,[]⟩ none) ⟨a,23,[]⟩ (some (scopeRef a))

def pending (t : Store Data) (a : Nat) (parents : List Frame)
    (loops : List LoopFrame) : Config :=
  let c := PV_THR2_StaticCall.pending (write (prepared t a) ⟨a,23,[]⟩ none)
    a parents (PV_THR2_F6.block86.drop 24) fn [scopeRef a] 22
  {c with frame := {c.frame with loops := loops}}

/-- Exactly8 own instructions ending at the actual source call request.
No callee implementation, prefix, final-store construction or fixed reply. -/
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (t : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (b : Bool)  (w : W) (es : List E) (stack : List Config) :
    PV_THR2_IntrinsicState.advance (PV_THR2_EntryDynamic.carrier base b) ctl P H 8
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.block86.drop 16,loops := loops},parents,t⟩,w,es⟩,stack⟩ =
      ⟨⟨.running (pending t a parents loops),w,es⟩,stack⟩ := by
  have shape : PV_THR2_F6.block86.drop 16 =
    [PV_THR2_F6.node70,PV_THR2_F6.node71,PV_THR2_F6.node72,PV_THR2_F6.node73,PV_THR2_F6.node74,PV_THR2_F6.node75,PV_THR2_F6.node76,PV_THR2_F6.node77] ++ PV_THR2_F6.block86.drop 24 := rfl
  rw [shape]
  generalize tail : PV_THR2_F6.block86.drop 24 = remaining
  have metadata : (PV_THR2_EntryDynamic.carrier base b).constant
      (.object [("kind",.object [("Adt",.array [.null,.array []])]),("ty",.object [("Deduplicated",.number 646)])]) = some .null := rfl
  have ref (q : Address) : (PV_THR2_EntryDynamic.carrier base b).reference q .null =
      PV_STX2_TypedReferences.reference q .null := rfl
  simp [
    PV_THR2_IntrinsicState.advance,PV_THR2_IntrinsicState.step,PV_THR2_Catch316Segment.select,
    PV_THR2_Execution.step,PV_THR2_Dynamic.active,PV_THR2_Dynamic.operandOf,
    PV_THR2_GapCompletion.step,PV_THR2_AggregateCompletion.complete,
    PV_THR2_AggregateCompletion.carrier,PV_STX2_SliceMachine.step,
    PV_THR2_F6.node70,PV_THR2_F6.node71,PV_THR2_F6.node72,PV_THR2_F6.node73,PV_THR2_F6.node74,PV_THR2_F6.node75,PV_THR2_F6.node76,PV_THR2_F6.node77,
    native,adopt,PV_STX2_Native.step,PV_STX2_Store.bind,evaluate,operands,operand,
    PV_STX2_Store.read,locate,writeAddress,write,metadata,ref,
    pending,prepared,scopeRef,fn,PV_THR2_StaticCall.pending,PV_THR2_StaticCall.issued,tail]

theorem frame (t : Store Data) (a : Nat) (q : Address) (outside : q.activation ≠ a) :
    (prepared t a).cells q = t.cells q := by
  have neq (i : Nat) : q ≠ (⟨a,i,[]⟩ : Address) := by
    intro eq
    exact outside (congrArg Address.activation eq)
  simp [prepared,write,neq]

#print axioms run
#print axioms frame
end PV_FN_THREAD_f6ParkDeref
