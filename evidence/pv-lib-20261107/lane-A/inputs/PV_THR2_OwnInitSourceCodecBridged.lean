import PV_THR2_BoxDynRepresentationBridge
import PV_THR2_OwnInitSourceCodec
set_option autoImplicit false
noncomputable section
namespace PV_THR2_OwnInitSourceCodec
open PV_STX2_Syntax PV_EVHB_OwnerMachine PV_OWN2_Codec
open scoped Classical
/-- New codec under thread21. The old codec and all its theorems are retained.
Both numeric inputs and tagged source Boxes retain partial decoding. -/
def decodeBridged (w : OWNER) : Data → Option PV_OWN2_ThreadInitLayout.InitWords
  | .object [("thread-aggregate-kind",kind),("thread-aggregate-slots",
      .array [.array [handle],.array [callback]])] =>
      if kind=PV_THR2_InitAggregate.kind then do
        let h ← PV_THR2_OwnInitPointerCodec.decode handle
        let (d,v) ← PV_THR2_BoxDynRepresentationBridge.decode w callback
        pure ⟨h,d,v⟩
      else none
  | _ => none
/-- Agreement includes malformed numeric words; no success is assumed. -/
theorem bare_agreement (w : OWNER) (kind handle data vtable : Data) :
    decodeBridged w (PV_THR2_KeyValues.pack kind [handle,.array [data,vtable]]) =
      decode (PV_THR2_KeyValues.pack kind [handle,.array [data,vtable]]) := by
  simp only [decodeBridged,decode,PV_THR2_KeyValues.pack,List.map_cons,List.map_nil,
    PV_THR2_BoxDynRepresentationBridge.decode]
  split
  · cases PV_THR2_OwnInitPointerCodec.decode handle <;>
      cases PV_THR2_OwnInitPointerCodec.decode data <;>
      cases PV_THR2_OwnInitPointerCodec.decode vtable <;> rfl
  · rfl

theorem source (w : OWNER) (symbols : PV_THR2_OperatorSemantics_14119.Symbols)
    (p : PV_STX2_Store.Address) (handle data : Pointer)
    (binding : PV_THR2_BoxDynRepresentationBridge.runtime w p = some data) :
    decodeBridged w (PV_THR2_KeyValues.pack PV_THR2_InitAggregate.kind
      [PV_THR2_OwnInitPointerCodec.encode handle,
        PV_THR2_BoxDynRepresentationBridge.callback symbols p]) =
      some ⟨handle,data,symbols.vtable_115⟩ := by
  have bridge := PV_THR2_BoxDynRepresentationBridge.source w symbols p data binding
  simp only [PV_THR2_BoxDynRepresentationBridge.Relates] at bridge
  simp only [decodeBridged,PV_THR2_KeyValues.pack,List.map_cons,List.map_nil,ite_true,
    PV_THR2_OwnInitPointerCodec.roundtrip,bridge,Bind.bind,Option.bind_some,Pure.pure]
#print axioms bare_agreement
#print axioms source
end PV_THR2_OwnInitSourceCodec
