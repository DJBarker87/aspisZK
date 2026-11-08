import PV_FN_THREAD_f6LoopBack
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f6LoopEntry
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_FN_THREAD_f6CompletionEntry (scopeRef fn)

def prepared (t : Store Data) (a : Nat) :=
  write (write (write (write (write (write t ⟨a,14,[]⟩ none)
    ⟨a,15,[]⟩ none) ⟨a,16,[]⟩ none) ⟨a,17,[]⟩ none)
    ⟨a,18,[]⟩ none) ⟨a,18,[]⟩ (some (scopeRef a))

def pending (t : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame) : Config :=
  let c := PV_THR2_StaticCall.pending (write (prepared t a) ⟨a,18,[]⟩ none)
    a parents (PV_THR2_F6.block86.drop 7) fn [scopeRef a] 17
  {c with frame := {c.frame with loops := loops}}

/-- Seven own source instructions at EVERY completion-loop iteration. The
loop's original saved exit and arbitrary lower caller stack are parameters.
No data read, successful child reply or termination premise is supplied. -/
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (t : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (b : Bool) (w : W) (es : List E) (stack : List Config) :
    PV_THR2_IntrinsicState.advance (PV_THR2_EntryDynamic.carrier base b) ctl P H 7
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.block86,loops := loops},parents,t⟩,w,es⟩,stack⟩ =
      ⟨⟨.running (pending t a parents loops),w,es⟩,stack⟩ := by
  have shape : PV_THR2_F6.block86 =
    [PV_THR2_F6.node51,PV_THR2_F6.node52,PV_THR2_F6.node53,PV_THR2_F6.node54,
      PV_THR2_F6.node55,PV_THR2_F6.node56,PV_THR2_F6.node57] ++ PV_THR2_F6.block86.drop 7 := rfl
  rw [shape]
  generalize tail : PV_THR2_F6.block86.drop 7 = remaining
  have metadata : (PV_THR2_EntryDynamic.carrier base b).constant
      (.object [("kind",.object [("Adt",.array [.null,.array []])]),("ty",.object [("Deduplicated",.number 646)])]) = some .null := rfl
  have ref (q : Address) : (PV_THR2_EntryDynamic.carrier base b).reference q .null =
      PV_STX2_TypedReferences.reference q .null := rfl
  simp [PV_THR2_IntrinsicState.advance,PV_THR2_IntrinsicState.step,PV_THR2_Catch316Segment.select,
    PV_THR2_Execution.step,PV_THR2_Dynamic.active,PV_THR2_Dynamic.operandOf,
    PV_THR2_GapCompletion.step,PV_THR2_AggregateCompletion.complete,
    PV_THR2_AggregateCompletion.carrier,PV_STX2_SliceMachine.step,
    PV_THR2_F6.node51,PV_THR2_F6.node52,PV_THR2_F6.node53,PV_THR2_F6.node54,
    PV_THR2_F6.node55,PV_THR2_F6.node56,PV_THR2_F6.node57,
    native,adopt,PV_STX2_Native.step,PV_STX2_Store.bind,evaluate,operands,operand,
    PV_STX2_Store.read,locate,writeAddress,write,metadata,ref,
    pending,prepared,scopeRef,fn,PV_THR2_StaticCall.pending,PV_THR2_StaticCall.issued,tail]

/-- The back edge and next own entry execute from128's arbitrary Post store;
no body of128 or126 is carried through the caller. -/
theorem reenter {W E : Type} (base : Carrier W Data) (ctl : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (t : Store Data) (a : Nat) (parents : List Frame)
    (afterLoop : List PV_STX2_SliceSyntax.Node) (lower : List LoopFrame)
    (b : Bool) (w : W) (es : List E) (stack : List Config) :
    let loops := (⟨PV_THR2_F6.block86,afterLoop⟩ : LoopFrame) :: lower
    PV_THR2_IntrinsicState.advance (PV_THR2_EntryDynamic.carrier base b) ctl P H 12
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.block86.drop 27,loops := loops},parents,t⟩,w,es⟩,stack⟩ =
      ⟨⟨.running (pending (PV_FN_THREAD_f6LoopBack.prepared t a) a parents loops),w,es⟩,stack⟩ := by
  dsimp only
  rw [show 12 = 5 + 7 from rfl,PV_THR2_IntrinsicComposition.advance_add,
    PV_FN_THREAD_f6LoopBack.run]
  exact run base ctl P H _ a parents _ b w es stack

theorem frame (t : Store Data) (a : Nat) (q : Address) (outside : q.activation ≠ a) :
    (prepared t a).cells q = t.cells q := by
  have neq (i : Nat) : q ≠ (⟨a,i,[]⟩ : Address) := by
    intro eq
    exact outside (congrArg Address.activation eq)
  simp [prepared,write,neq]

#print axioms run
#print axioms reenter
#print axioms frame
end PV_FN_THREAD_f6LoopEntry
