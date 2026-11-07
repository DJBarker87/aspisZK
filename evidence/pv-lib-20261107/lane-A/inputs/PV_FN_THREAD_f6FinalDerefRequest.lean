import PV_FN_THREAD_f6LoopBack
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f6FinalDerefRequest
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
def scopeRef (a : Nat) := PV_STX2_TypedReferences.reference ⟨a,2,[0]⟩ .null

def fn : Data := match PV_THR2_F6.node120 with
  | .leaf (.call _ f _ _ _) => f | _ => .null

def prepared (t : Store Data) (a : Nat) :=
  write (write (write (write (write (write (write (write t
    ⟨a,17,[]⟩ none) ⟨a,15,[]⟩ none) ⟨a,14,[]⟩ none)
    ⟨a,28,[]⟩ none) ⟨a,29,[]⟩ none) ⟨a,30,[]⟩ none)
    ⟨a,31,[]⟩ none) ⟨a,31,[]⟩ (some (scopeRef a))

def pending (t : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame) : Config :=
  let c := PV_THR2_StaticCall.pending (write (prepared t a) ⟨a,31,[]⟩ none)
    a parents (PV_THR2_F6.live.body.drop 62) fn [scopeRef a] 30
  {c with frame := {c.frame with loops := loops}}

/-- Ten own instructions after loop exit on the Ok125 branch. The result
cell and discriminant are INTERNAL125 Post projections, not f6 Pre.
No126 body, final store, or successful126 answer is assumed. -/
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (t : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (b : Bool) (result : Data) (w : W) (es : List E) (stack : List Config)
    (result_cell : t.cells ⟨a,10,[]⟩ = some result)
    (ok_case : ctl.variant result = some 0) :
    PV_THR2_IntrinsicState.advance (PV_THR2_EntryDynamic.carrier base b) ctl P H 10
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.live.body.drop 52,loops := loops},parents,t⟩,w,es⟩,stack⟩ =
      ⟨⟨.running (pending t a parents loops),w,es⟩,stack⟩ := by
  have shape : PV_THR2_F6.live.body.drop 52 =
    [PV_THR2_F6.node88,PV_THR2_F6.node89,PV_THR2_F6.node90,PV_THR2_F6.node114,
      PV_THR2_F6.node115,PV_THR2_F6.node116,PV_THR2_F6.node117,PV_THR2_F6.node118,
      PV_THR2_F6.node119,PV_THR2_F6.node120] ++ PV_THR2_F6.live.body.drop 62 := rfl
  rw [shape]
  generalize tail : PV_THR2_F6.live.body.drop 62 = remaining
  have metadata : (PV_THR2_EntryDynamic.carrier base b).constant
      (.object [("kind",.object [("Adt",.array [.null,.array []])]),("ty",.object [("Deduplicated",.number 646)])]) = some .null := rfl
  have ref (q : Address) : (PV_THR2_EntryDynamic.carrier base b).reference q .null =
      PV_STX2_TypedReferences.reference q .null := rfl
  simp [PV_THR2_IntrinsicState.advance,PV_THR2_IntrinsicState.step,PV_THR2_Catch316Segment.select,
    PV_THR2_Execution.step,PV_THR2_Dynamic.active,PV_THR2_Dynamic.operandOf,
    PV_THR2_GapCompletion.step,PV_THR2_AggregateCompletion.complete,
    PV_THR2_AggregateCompletion.carrier,PV_STX2_SliceMachine.step,
    PV_THR2_F6.node88,PV_THR2_F6.node89,PV_THR2_F6.node90,PV_THR2_F6.node114,
    PV_THR2_F6.node115,PV_THR2_F6.node116,PV_THR2_F6.node117,PV_THR2_F6.node118,
    PV_THR2_F6.node119,PV_THR2_F6.node120,PV_THR2_F6.block91,
    native,adopt,PV_STX2_Native.step,PV_STX2_Store.bind,evaluate,operands,operand,
    PV_STX2_Store.read,locate,writeAddress,write,metadata,ref,result_cell,ok_case,selectVariant,
    pending,prepared,scopeRef,fn,PV_THR2_StaticCall.pending,PV_THR2_StaticCall.issued,tail]


#print axioms run
end PV_FN_THREAD_f6FinalDerefRequest
