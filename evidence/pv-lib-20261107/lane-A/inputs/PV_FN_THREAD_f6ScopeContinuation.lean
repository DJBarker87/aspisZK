import PV_FN_THREAD_f6ArcContinuation
import PV_THR2_ScopeCaptureWrap
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f6ScopeContinuation
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine

open PV_THR2_ScopeValue in
/-- Reuse the exact source segment in the full intrinsic interpreter on an arbitrary explicit store. Internal cell facts are discharged by the caller composition. -/
theorem scope {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a : Nat) (parents : List Frame) (b : Bool) (arc : Data) (w : W) (es : List E) (stack : List Config)
    (cell : s.cells ⟨a,3,[]⟩ = some arc) :
    PV_THR2_IntrinsicState.advance (PV_THR2_EntryDynamic.carrier base b) ctl programs handler 9
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.live.body.drop 26},parents,s⟩,w,es⟩,stack⟩ =
    ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.live.body.drop 35},parents,prepared s a arc⟩,w,es⟩,stack⟩ := by
  have shape : PV_THR2_F6.live.body.drop 26 =
    [PV_THR2_F6.node26,PV_THR2_F6.node27,PV_THR2_F6.node28,PV_THR2_F6.node29,
      PV_THR2_F6.node30,PV_THR2_F6.node31,PV_THR2_F6.node32,PV_THR2_F6.node33,PV_THR2_F6.node34] ++ PV_THR2_F6.live.body.drop 35 := rfl
  rw [shape]
  generalize tail : PV_THR2_F6.live.body.drop 35 = remaining
  have k8 : (PV_THR2_EntryDynamic.carrier base b).aggregate kinds.1 [] = none := rfl
  have k9 : (PV_THR2_EntryDynamic.carrier base b).aggregate kinds.2.1 [] = none := rfl
  have k2 : (PV_THR2_EntryDynamic.carrier base b).aggregate kinds.2.2
      [arc,PV_THR2_KeyValues.pack kinds.2.1 [],PV_THR2_KeyValues.pack kinds.1 []] = none := rfl
  simp only [kinds,PV_THR2_F6.node28,PV_THR2_F6.node30,PV_THR2_F6.node31] at k8 k9 k2
  simp [PV_THR2_IntrinsicState.advance,PV_THR2_IntrinsicState.step,PV_THR2_Catch316Segment.select,PV_THR2_Execution.advance,PV_THR2_Execution.step,PV_THR2_Dynamic.active,
    PV_THR2_GapCompletion.step,PV_THR2_AggregateCompletion.complete,PV_THR2_AggregateCompletion.carrier,
    PV_STX2_SliceMachine.step,PV_THR2_F6.node26,PV_THR2_F6.node27,PV_THR2_F6.node28,
    PV_THR2_F6.node29,PV_THR2_F6.node30,PV_THR2_F6.node31,PV_THR2_F6.node32,PV_THR2_F6.node33,PV_THR2_F6.node34,
    native,adopt,PV_STX2_Native.step,PV_STX2_Store.bind,evaluate,operands,operand,
    PV_STX2_Store.read,locate,writeAddress,write,cell,k8,k9,k2,prepared,value,kinds]

#print axioms scope

open PV_THR2_ScopeCapturePrefix in
/-- Reuse the exact source segment in the full intrinsic interpreter on an arbitrary explicit store. Internal cell facts are discharged by the caller composition. -/
theorem reference {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a : Nat) (parents : List Frame) (b : Bool) (w : W) (es : List E) (stack : List Config) :
    PV_THR2_IntrinsicState.advance (PV_THR2_EntryDynamic.carrier base b) ctl programs handler 6
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.live.body.drop 35},parents,s⟩,w,es⟩,stack⟩ =
    ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.live.body.drop 41},parents,prepared s a⟩,w,es⟩,stack⟩ := by
  have shape : PV_THR2_F6.live.body.drop 35 =
    [PV_THR2_F6.node35,PV_THR2_F6.node36,PV_THR2_F6.node37,PV_THR2_F6.node38,
      PV_THR2_F6.node39,PV_THR2_F6.node40] ++ PV_THR2_F6.live.body.drop 41 := rfl
  rw [shape]
  generalize tail : PV_THR2_F6.live.body.drop 41 = remaining
  have metadata : (PV_THR2_EntryDynamic.carrier base b).constant
      (.object [("kind",.object [("Adt",.array [.null,.array []])]),("ty",.object [("Deduplicated",.number 646)])]) = some .null := rfl
  have ref (p : Address) : (PV_THR2_EntryDynamic.carrier base b).reference p .null =
      PV_STX2_TypedReferences.reference p .null := rfl
  have flag : (PV_THR2_EntryDynamic.carrier base b).constant
      (.object [("kind",.object [("Literal",.object [("Bool",.boolean false)])]),("ty",.object [("Deduplicated",.number 556)])]) = some (.boolean false) := rfl
  simp [PV_THR2_IntrinsicState.advance,PV_THR2_IntrinsicState.step,PV_THR2_Catch316Segment.select,PV_THR2_Execution.advance,PV_THR2_Execution.step,PV_THR2_Dynamic.active,
    PV_THR2_GapCompletion.step,PV_THR2_AggregateCompletion.complete,PV_STX2_SliceMachine.step,
    PV_THR2_F6.node35,PV_THR2_F6.node36,PV_THR2_F6.node37,PV_THR2_F6.node38,PV_THR2_F6.node39,PV_THR2_F6.node40,
    native,adopt,PV_STX2_Native.step,PV_STX2_Store.bind,evaluate,operand,
    PV_STX2_Store.read,locate,writeAddress,write,metadata,ref,flag,prepared]

#print axioms reference

open PV_THR2_ScopeCaptureWrap in
/-- Reuse the exact source segment in the full intrinsic interpreter on an arbitrary explicit store. Internal cell facts are discharged by the caller composition. -/
theorem wrap {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a : Nat) (parents : List Frame) (b : Bool) (captured : Data) (w : W) (es : List E) (stack : List Config)
    (c1 : s.cells ⟨a,1,[]⟩ = some captured)
    (c13 : s.cells ⟨a,13,[]⟩ = some (PV_STX2_TypedReferences.reference ⟨a,2,[]⟩ .null)) :
    PV_THR2_IntrinsicState.advance (PV_THR2_EntryDynamic.carrier base b) ctl programs handler 4
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.live.body.drop 41},parents,s⟩,w,es⟩,stack⟩ =
    ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.live.body.drop 45},parents,prepared s a captured⟩,w,es⟩,stack⟩ := by
  have shape : PV_THR2_F6.live.body.drop 41 =
    [PV_THR2_F6.node41,PV_THR2_F6.node42,PV_THR2_F6.node43,PV_THR2_F6.node44] ++ PV_THR2_F6.live.body.drop 45 := rfl
  rw [shape]
  generalize tail : PV_THR2_F6.live.body.drop 45 = remaining
  have k12 : (PV_THR2_EntryDynamic.carrier base b).aggregate kinds.1
      [captured,PV_STX2_TypedReferences.reference ⟨a,2,[]⟩ .null] = none := rfl
  have k11 : (PV_THR2_EntryDynamic.carrier base b).aggregate kinds.2 [inner a captured] = none := rfl
  simp only [inner,kinds,PV_THR2_F6.node41,PV_THR2_F6.node43] at k12 k11
  simp [PV_THR2_IntrinsicState.advance,PV_THR2_IntrinsicState.step,PV_THR2_Catch316Segment.select,PV_THR2_Execution.advance,PV_THR2_Execution.step,PV_THR2_Dynamic.active,
    PV_THR2_GapCompletion.step,PV_THR2_AggregateCompletion.complete,PV_THR2_AggregateCompletion.carrier,
    PV_STX2_SliceMachine.step,PV_THR2_F6.node41,PV_THR2_F6.node42,PV_THR2_F6.node43,PV_THR2_F6.node44,
    native,adopt,PV_STX2_Native.step,PV_STX2_Store.bind,evaluate,operands,operand,
    PV_STX2_Store.read,locate,writeAddress,write,c1,c13,k12,k11,prepared,value,inner,kinds]

#print axioms wrap
end PV_FN_THREAD_f6ScopeContinuation
