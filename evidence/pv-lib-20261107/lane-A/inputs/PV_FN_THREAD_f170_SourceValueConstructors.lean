import PV_FN_THREAD_f164
import PV_FN_THREAD_f170_ActualNativeFrames
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f170
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_W1_LeafBoundary PV_W1_OwnerNativeFrame

/-- Source ADT constructors. The type descriptor is explicit; the representation
is the existing source pack, never an opaque backend marker. -/
def sourceTlsKind (ty : Data) (variant : Nat) : Data :=
  .object [("Adt",.array [ty,.number variant,.null])]

/-- AccessError's empty constructor is read from the actual emitted8059. -/
def sourceTlsAccessErrorKind : Data := match PV_THR2_F170.node19 with
  | .leaf (.aggregateMove _ _ kind _) => kind
  | _ => .null

inductive SourceTlsValue where
  | pointer (p : Address)
  | optionNone (ty : Data)
  | optionSome (ty : Data) (p : Address)
  | resultOk (ty : Data) (p : Address)
  | resultErr (ty : Data)
  | controlContinue (ty : Data) (p : Address)
  | controlBreak (ty residualTy : Data)

def SourceTlsValue.encode : SourceTlsValue → Data
  | .pointer p => PV_STX2_TypedReferences.reference p .null
  | .optionNone ty => PV_THR2_KeyValues.pack (sourceTlsKind ty 0) []
  | .optionSome ty p => PV_THR2_KeyValues.pack (sourceTlsKind ty 1)
      [PV_STX2_TypedReferences.reference p .null]
  | .resultOk ty p => PV_THR2_KeyValues.pack (sourceTlsKind ty 0)
      [PV_STX2_TypedReferences.reference p .null]
  | .resultErr ty => PV_THR2_KeyValues.pack (sourceTlsKind ty 1)
      [PV_THR2_KeyValues.pack sourceTlsAccessErrorKind []]
  | .controlContinue ty p => PV_THR2_KeyValues.pack (sourceTlsKind ty 0)
      [PV_STX2_TypedReferences.reference p .null]
  | .controlBreak ty residualTy => PV_THR2_KeyValues.pack (sourceTlsKind ty 1)
      [PV_THR2_KeyValues.pack (sourceTlsKind residualTy 1)
        [PV_THR2_KeyValues.pack sourceTlsAccessErrorKind []]]

inductive SourceTlsShape where
  | pointer | option | result | controlFlow

def SourceTlsValue.shape : SourceTlsValue → SourceTlsShape
  | .pointer _ => .pointer
  | .optionNone _ | .optionSome _ _ => .option
  | .resultOk _ _ | .resultErr _ => .result
  | .controlContinue _ _ | .controlBreak _ _ => .controlFlow

/-- Only source-encoded reference constructors carry a TLS address. -/
def SourceTlsValue.InRegion (region : Address → Prop) : SourceTlsValue → Prop
  | .pointer p | .optionSome _ p | .resultOk _ p | .controlContinue _ p => region p
  | .optionNone _ | .resultErr _ | .controlBreak _ _ => True

def SourceEncodedTlsValue (region : Address → Prop) (v : Data) : Prop :=
  ∃ source : SourceTlsValue, v = source.encode ∧ source.InRegion region

def SourceTypedTlsValue (shape : SourceTlsShape) (region : Address → Prop) (v : Data) : Prop :=
  ∃ source : SourceTlsValue, source.shape = shape ∧ v = source.encode ∧ source.InRegion region

/-- Pointer decoding is determined by the SOURCE constructor at every world.
This is derived from typed-reference roundtrip, not a stability premise. -/
theorem source_tls_pointer {W : Type} (base : Carrier W Data) (b : Bool)
    (w : W) (p : Address) :
    (PV_FN_THREAD_f164.carrier base b).dereference w
      (SourceTlsValue.pointer p).encode = some p := by
  change (PV_STX2_TypedReferences.carrier _).dereference w
    (PV_STX2_TypedReferences.reference p .null) = some p
  exact PV_STX2_TypedReferences.dereference _ w p .null

/-- The exact field selected at8136 is the source reference, independently
of any later backend world or a fallback interpretation. -/
theorem source_tls_continue_field {W : Type} (base : Carrier W Data) (b : Bool)
    (ty : Data) (p : Address) :
    (PV_FN_THREAD_f164.carrier base b).field
      (SourceTlsValue.controlContinue ty p).encode 0 =
      some (SourceTlsValue.pointer p).encode := rfl

/-- Source ControlFlow discriminants preserve Continue and Break. A caller's
machine specification must use its named source-control interpretation. -/
theorem source_tls_flow_variants (base : Control) (ty residualTy : Data) (p : Address) :
    (PV_THR2_ThreadFields.control base).variant
      (SourceTlsValue.controlContinue ty p).encode = some 0 ∧
    (PV_THR2_ThreadFields.control base).variant
      (SourceTlsValue.controlBreak ty residualTy).encode = some 1 := ⟨rfl,rfl⟩

#print axioms source_tls_pointer
#print axioms source_tls_continue_field
#print axioms source_tls_flow_variants
end PV_FN_THREAD_f170
