import PV_FN_THREAD_f361BoxCallees
import PV_THR2_OperatorSemantics_14119
import PV_THR2_OperatorSemantics_14121
import PV_THR2_OperatorSemantics_14318
import PV_THR2_OperatorSemantics_14541
import PV_THR2_OwnInitSourceCodec
import PV_THR2_OwnInitAllocationHandler
import PV_THR2_TypedRepresentation_BoxDynFnOnce
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f361BoxCodecGap
open PV_STX2_Syntax PV_STX2_Store PV_OWN2_Codec

/-- The exact CLOSED443 successful source value is not a native word.
This statement is about the existing representations, not Rust pointer validity. -/
theorem reference_decode (p : Address) :
    PV_THR2_OwnInitPointerCodec.decode
      (PV_STX2_TypedReferences.reference p .null) = none := rfl

/-- The four required casts preserve the source-reference data part. -/
def callback (symbols : PV_THR2_OperatorSemantics_14119.Symbols) (p : Address) : Data :=
  PV_THR2_OperatorSemantics_14541.result
    (PV_THR2_OperatorSemantics_14318.result
      (PV_THR2_OperatorSemantics_14121.result
        (PV_THR2_OperatorSemantics_14119.result symbols
          (PV_STX2_TypedReferences.reference p .null))))

theorem callback_value (symbols : PV_THR2_OperatorSemantics_14119.Symbols) (p : Address) :
    callback symbols p = .array [PV_STX2_TypedReferences.reference p .null,
      PV_THR2_OperatorSemantics_14119.vtable_115 symbols] := rfl

/-- Even a represented Thread and the exact named vtable do not make the
source-address data part acceptable to the existing14756 source codec. -/
theorem init_decode (symbols : PV_THR2_OperatorSemantics_14119.Symbols)
    (p : Address) (handle : Pointer) :
    PV_THR2_OwnInitSourceCodec.decode
      (PV_THR2_KeyValues.pack PV_THR2_InitAggregate.kind
        [PV_THR2_OwnInitPointerCodec.encode handle,callback symbols p]) = none := by
  rw [callback_value]
  simp only [PV_THR2_OwnInitSourceCodec.decode,PV_THR2_KeyValues.pack,
    List.map_cons,List.map_nil,ite_true,
    PV_THR2_OwnInitPointerCodec.roundtrip,reference_decode,
    Option.bind_some,Option.bind_none,Bind.bind]

/-- Actual458/537 return representation. This wrapper remains present across
14318 and14541, even with the exact612 primitive fact installed. -/
def boxedCallback (unique allocator : Data) : Data :=
  PV_THR2_OperatorSemantics_14541.result
    (PV_THR2_OperatorSemantics_14318.result
      (PV_THR2_Box537Suffix13.boxed unique allocator))

/-- The existing allocation decoder rejects the actual Box constructor tag,
independently of every payload word and every address. -/
theorem boxed_init_decode (unique allocator thread : Data) :
    PV_THR2_OwnInitSourceCodec.decode
      (PV_THR2_KeyValues.pack PV_THR2_InitAggregate.kind
        [thread,boxedCallback unique allocator]) = none := rfl

theorem boxed_no_numeric_shape (unique allocator : Data) :
    ¬ PV_THR2_TypedRepresentation_BoxDynFnOnce.Shape
      (boxedCallback unique allocator) := by
  rintro ⟨data,vtable,equal⟩
  cases equal

/-- The actual allocation interpretation takes its fallback on this source
Box constructor value, even when the receiver/header lookup would succeed. -/
theorem allocation_falls_back
    (resources : PV_EVHB_OwnerHeap.Resources) (encode : PV_EVHB_OwnerHeap.Encode)
    (fallback : PV_STX2_Native.Request Data → PV_EVHB_OwnerMachine.OWNER →
      PV_STX_Machine.Reply PV_EVHB_OwnerMachine.OWNER PV_RJ4IDB.NativeEvent Data)
    (unique allocator thread : Data) (a : Nat) (w : PV_EVHB_OwnerMachine.OWNER) :
    PV_THR2_OwnInitAllocationHandler.handler resources encode fallback
      (.child PV_THR2_Source361InitChildren.fnAllocationFull a
        [PV_THR2_KeyValues.pack PV_THR2_InitAggregate.kind
          [thread,boxedCallback unique allocator]]) w =
      fallback (.child PV_THR2_Source361InitChildren.fnAllocationFull a
        [PV_THR2_KeyValues.pack PV_THR2_InitAggregate.kind
          [thread,boxedCallback unique allocator]]) w := by
  simp only [PV_THR2_OwnInitAllocationHandler.handler,ite_true,boxed_init_decode]

/-- Reuse CLOSED458 at its actual14313 call context. On every successful612
branch the precise source Box output is outside the numeric Box shape and is
rejected by14756's decoder. No458/537 instruction is re-walked. -/
theorem at14313 {E : Type} (x : PV_FN_THREAD_f361BoxCallees.Input E)
    (raw thread : Data)
    (owner : PV_FN_THREAD_OwnerWellFormed.OwnerWellFormed x.w x.s.nextActivation)
    (unique612 : PV_THR2_IntrinsicSemantics_UniqueNewUnchecked612.Fact x.native) :
    let y := PV_FN_THREAD_f361BoxCallees.child458 x raw
    PV_FN_THREAD_f458.PostWithPointer y ∧
    (∀ unique, (PV_FN_THREAD_f537.reply (PV_FN_THREAD_f458Entry.child y)).answer =
      .returned (.ok unique) →
      PV_FN_THREAD_f458.boxPointer
        (PV_THR2_Box537Suffix13.boxed unique PV_THR2_Box458Prefix5.allocator) = some raw ∧
      ¬ PV_THR2_TypedRepresentation_BoxDynFnOnce.Shape
        (boxedCallback unique PV_THR2_Box458Prefix5.allocator) ∧
      PV_THR2_OwnInitSourceCodec.decode
        (PV_THR2_KeyValues.pack PV_THR2_InitAggregate.kind
          [thread,boxedCallback unique PV_THR2_Box458Prefix5.allocator]) = none) := by
  dsimp only
  have closed := PV_FN_THREAD_f361BoxCallees.callee458 x raw owner unique612
  refine ⟨closed,?_⟩
  intro unique returned
  exact ⟨(closed.2 unique returned).1,boxed_no_numeric_shape _ _,boxed_init_decode _ _ _⟩

/-- Adding a delivered numeric Box shape for this exact source value would
be contradictory; it cannot discharge the missing representation bridge. -/
theorem no_numeric_shape (symbols : PV_THR2_OperatorSemantics_14119.Symbols)
    (p : Address) :
    ¬ PV_THR2_TypedRepresentation_BoxDynFnOnce.Shape (callback symbols p) := by
  rintro ⟨data,vtable,equal⟩
  have dataEq : PV_STX2_TypedReferences.reference p .null =
      PV_THR2_OwnInitPointerCodec.encode data := by
    have arrays := Data.array.inj equal
    exact (List.cons.inj arrays).1
  have decoded := congrArg PV_THR2_OwnInitPointerCodec.decode dataEq
  rw [reference_decode,PV_THR2_OwnInitPointerCodec.roundtrip] at decoded
  cases decoded

#print axioms allocation_falls_back
#print axioms at14313
#print axioms boxed_init_decode
#print axioms boxed_no_numeric_shape
#print axioms reference_decode
#print axioms callback_value
#print axioms init_decode
#print axioms no_numeric_shape
end PV_FN_THREAD_f361BoxCodecGap
