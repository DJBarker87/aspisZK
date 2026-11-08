import PV_FN_THREAD_f6CounterTest
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f6FlagRequest
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine

/-- Exact emitted call129 descriptor at source2759. -/
def fn : Data := match PV_THR2_F6.node125 with
  | .leaf (.call _ f _ _ _) => f | _ => .null

def flagRef (p : Address) := PV_STX2_TypedReferences.reference {p with fields := p.fields ++ [1]} .null
/-- Only f6's own local writes, on the preceding callee's explicit Post store. -/
def orderingKind : Data := match PV_THR2_F6.node124 with
  | .leaf (.aggregateMove _ _ k _) => k | _ => .null

def prepared (t : Store Data) (a : Nat) (p : Address) :=
  write (write (write (write t ⟨a,31,[]⟩ none)
    ⟨a,29,[]⟩ (some (flagRef p))) ⟨a,32,[]⟩ none)
    ⟨a,32,[]⟩ (some (PV_THR2_KeyValues.pack orderingKind []))

def pending (t : Store Data) (a : Nat) (parents : List Frame)
    (loops : List LoopFrame) (p : Address) : Config :=
  let c := PV_THR2_StaticCall.pending (write (write (prepared t a p) ⟨a,29,[]⟩ none) ⟨a,32,[]⟩ none)
    a parents (PV_THR2_F6.live.body.drop 67) fn [flagRef p,PV_THR2_KeyValues.pack orderingKind []] 28
  {c with frame := {c.frame with loops := loops}}

/-- Exactly5 own instructions ending at the actual source call request.
No callee implementation, prefix, final-store construction or fixed reply. -/
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (t : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (b : Bool) (p : Address) (w : W) (es : List E) (stack : List Config)
    (root_cell : t.cells ⟨a,30,[]⟩ = some (PV_STX2_TypedReferences.reference p .null)) :
    PV_THR2_IntrinsicState.advance (PV_THR2_EntryDynamic.carrier base b) ctl P H 5
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.live.body.drop 62,loops := loops},parents,t⟩,w,es⟩,stack⟩ =
      ⟨⟨.running (pending t a parents loops p),w,es⟩,stack⟩ := by
  have shape : PV_THR2_F6.live.body.drop 62 =
    [PV_THR2_F6.node121,PV_THR2_F6.node122,PV_THR2_F6.node123,PV_THR2_F6.node124,PV_THR2_F6.node125] ++ PV_THR2_F6.live.body.drop 67 := rfl
  rw [shape]
  generalize tail : PV_THR2_F6.live.body.drop 67 = remaining
  have metadata : (PV_THR2_EntryDynamic.carrier base b).constant
      (.object [("kind",.object [("Adt",.array [.null,.array []])]),("ty",.object [("Deduplicated",.number 646)])]) = some .null := rfl
  have ref (q : Address) : (PV_THR2_EntryDynamic.carrier base b).reference q .null =
      PV_STX2_TypedReferences.reference q .null := rfl
  have deref : (PV_THR2_EntryDynamic.carrier base b).dereference w
      (PV_STX2_TypedReferences.reference p .null) = some p :=
    PV_STX2_TypedReferences.dereference _ w p .null
  have agg : (PV_THR2_EntryDynamic.carrier base b).aggregate orderingKind [] = none := rfl
  simp only [orderingKind,PV_THR2_F6.node124] at agg
  simp [
    PV_THR2_IntrinsicState.advance,PV_THR2_IntrinsicState.step,PV_THR2_Catch316Segment.select,
    PV_THR2_Execution.step,PV_THR2_Dynamic.active,PV_THR2_Dynamic.operandOf,
    PV_THR2_GapCompletion.step,PV_THR2_AggregateCompletion.complete,
    PV_THR2_AggregateCompletion.carrier,PV_STX2_SliceMachine.step,
    PV_THR2_F6.node121,PV_THR2_F6.node122,PV_THR2_F6.node123,PV_THR2_F6.node124,PV_THR2_F6.node125,
    native,adopt,PV_STX2_Native.step,PV_STX2_Store.bind,evaluate,operands,operand,
    PV_STX2_Store.read,locate,writeAddress,write,metadata,ref,deref,root_cell,agg,
    pending,prepared,flagRef,orderingKind,fn,PV_THR2_StaticCall.pending,PV_THR2_StaticCall.issued,tail]

theorem frame (t : Store Data) (a : Nat) (p : Address) (q : Address) (outside : q.activation ≠ a) :
    (prepared t a p).cells q = t.cells q := by
  have neq (i : Nat) : q ≠ (⟨a,i,[]⟩ : Address) := by
    intro eq
    exact outside (congrArg Address.activation eq)
  simp [prepared,write,neq]

#print axioms run
#print axioms frame
end PV_FN_THREAD_f6FlagRequest
