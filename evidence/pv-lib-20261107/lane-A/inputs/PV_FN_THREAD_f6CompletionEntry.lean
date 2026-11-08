import PV_FN_THREAD_f6OwnContinuation
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f6CompletionEntry
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine

/-- Source2097's descriptor, not the different126 instantiations later in f6. -/
def fn : Data := match PV_THR2_F6.node57 with
  | .leaf (.call _ f _ _ _) => f | _ => .null

def scopeRef (a : Nat) := PV_STX2_TypedReferences.reference ⟨a,2,[0]⟩ .null

/-- f6's five own guard/lifetime writes after the125 reply. -/
def guards (t : Store Data) (a : Nat) : Store Data :=
  write (write (write (write (write t ⟨a,35,[]⟩ (some (.boolean true)))
    ⟨a,36,[]⟩ (some (.boolean true))) ⟨a,37,[]⟩ (some (.boolean true)))
    ⟨a,38,[]⟩ (some (.boolean true))) ⟨a,11,[]⟩ none

/-- Only source loop storage and reference creation; no126 implementation. -/
def prepared (t : Store Data) (a : Nat) : Store Data :=
  write (write (write (write (write (write (guards t a)
    ⟨a,14,[]⟩ none) ⟨a,15,[]⟩ none) ⟨a,16,[]⟩ none) ⟨a,17,[]⟩ none)
    ⟨a,18,[]⟩ none) ⟨a,18,[]⟩ (some (scopeRef a))

def pending (t : Store Data) (a : Nat) (parents : List Frame) : Config :=
  ⟨{activation := a,remaining := PV_THR2_F6.block86.drop 7,
    loops := [⟨PV_THR2_F6.block86,PV_THR2_F6.live.body.drop 52⟩],
    waiting := some (PV_THR2_StaticReply.wait (prepared t a) fn [scopeRef a] 17)},parents,
    PV_THR2_StaticCall.issued (write (prepared t a) ⟨a,18,[]⟩ none) [scopeRef a]⟩

/-- After an arbitrary125 Post, execute exactly13 f6 instructions: four guards,
one lifetime, loop entry, five loop locals, source-derived scope reference and
source2097 call issuance. All saved callers/world/events remain exact. -/
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (t : Store Data) (a : Nat) (parents : List Frame) (b : Bool)
    (w : W) (es : List E) (stack : List Config) :
    PV_THR2_IntrinsicState.advance (PV_THR2_EntryDynamic.carrier base b) ctl P H 13
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.live.body.drop 46},parents,t⟩,w,es⟩,stack⟩ =
      ⟨⟨.running (pending t a parents),w,es⟩,stack⟩ := by
  have shape : PV_THR2_F6.live.body.drop 46 =
    [PV_THR2_F6.node46,PV_THR2_F6.node47,PV_THR2_F6.node48,PV_THR2_F6.node49,
      PV_THR2_F6.node50,PV_THR2_F6.node87] ++ PV_THR2_F6.live.body.drop 52 := rfl
  have loopShape : PV_THR2_F6.block86 =
    [PV_THR2_F6.node51,PV_THR2_F6.node52,PV_THR2_F6.node53,PV_THR2_F6.node54,
      PV_THR2_F6.node55,PV_THR2_F6.node56,PV_THR2_F6.node57] ++ PV_THR2_F6.block86.drop 7 := rfl
  rw [shape]
  simp only [PV_THR2_F6.node87]
  rw [loopShape]
  generalize tail : PV_THR2_F6.live.body.drop 52 = afterLoop
  generalize rest : PV_THR2_F6.block86.drop 7 = remaining
  have flag : (PV_THR2_EntryDynamic.carrier base b).constant
      (.object [("kind",.object [("Literal",.object [("Bool",.boolean true)])]),("ty",.object [("Deduplicated",.number 556)])]) = some (.boolean true) := rfl
  have metadata : (PV_THR2_EntryDynamic.carrier base b).constant
      (.object [("kind",.object [("Adt",.array [.null,.array []])]),("ty",.object [("Deduplicated",.number 646)])]) = some .null := rfl
  have ref (p : Address) : (PV_THR2_EntryDynamic.carrier base b).reference p .null =
      PV_STX2_TypedReferences.reference p .null := rfl
  simp [PV_THR2_IntrinsicState.advance,PV_THR2_IntrinsicState.step,PV_THR2_Catch316Segment.select,
    PV_THR2_Execution.step,PV_THR2_Dynamic.active,PV_THR2_Dynamic.operandOf,
    PV_THR2_GapCompletion.step,PV_THR2_AggregateCompletion.complete,
    PV_STX2_SliceMachine.step,PV_THR2_F6.node46,PV_THR2_F6.node47,PV_THR2_F6.node48,
    PV_THR2_F6.node49,PV_THR2_F6.node50,PV_THR2_F6.node51,PV_THR2_F6.node52,
    PV_THR2_F6.node53,PV_THR2_F6.node54,PV_THR2_F6.node55,PV_THR2_F6.node56,PV_THR2_F6.node57,
    native,adopt,PV_STX2_Native.step,PV_STX2_Store.bind,evaluate,operands,operand,
    PV_STX2_Store.read,locate,writeAddress,write,flag,metadata,ref,
    pending,prepared,guards,scopeRef,fn,PV_THR2_StaticReply.wait,
    PV_THR2_StaticCall.issued,tail,rest]
  rw [← rest]
  exact loopShape.symm

/-- Own loop-prefix writes frame every other activation. -/
theorem frame (t : Store Data) (a : Nat) (p : Address) (outside : p.activation ≠ a) :
    (prepared t a).cells p = t.cells p := by
  have neq (i : Nat) : p ≠ (⟨a,i,[]⟩ : Address) := by
    intro eq
    exact outside (congrArg Address.activation eq)
  simp [prepared,guards,write,neq]

#print axioms run
#print axioms frame
end PV_FN_THREAD_f6CompletionEntry
