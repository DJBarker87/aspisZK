import PV_FN_THREAD_f458Closed
import PV_THR2_OperatorSemantics_14119
import PV_THR2_OperatorSemantics_14121
import PV_THR2_OperatorSemantics_14318
import PV_THR2_OperatorSemantics_14541
set_option autoImplicit false
noncomputable section
namespace PV_THR2_BoxDynRepresentationBridge
open PV_STX2_Syntax PV_STX2_Store PV_EVHB_OwnerMachine PV_OWN2_Codec
open scoped Classical
/-- Recount14 typed_representation, thread21. On rustc14210df0 (nightly
2026-06-01), Box<dyn FnOnce> has data then vtable; Unique/NonNull and Global
add no runtime words. The emitted impl115/39260 symbol is the linkage constant
in OperatorSemantics_14119.Symbols. Its identification in fc8808eb is a named
binary-structural obligation, not a successful-run hypothesis. The binary
layout evidence is pv-own2-20261104/layout-D690/check-layout-D690.py.
No source reference is converted by its activation number or by value search. -/
def sourcePlace (p : Address) : PV_EVHB_OwnerMachine.Place := ⟨p.activation,p.localIndex :: p.fields⟩
/-- The registry header supplies the physical address; missing bindings and
out-of-range words remain failures. This implies no allocation validity. -/
def runtime (w : OWNER) (p : Address) : Option Pointer := do
  let (_,h) ← receiver w (sourcePlace p)
  PV_THR2_OwnInitPointerCodec.decode (.number h.pointer)
/-- Use the provider's own Box/Unique projections, preserving both source tags
as logical wrappers. Source reference metadata does not become a numeric word. -/
def sourceWords (w : OWNER) (value : Data) : Option (Pointer × Pointer) := do
  let raw ← PV_FN_THREAD_f458.boxPointer value
  match raw with
  | .array [data,vtable] =>
    let (p,_) ← PV_STX2_TypedReferences.decode data
    let d ← runtime w p
    let v ← PV_THR2_OwnInitPointerCodec.decode vtable
    pure (d,v)
  | _ => none
/-- Bare numeric pairs retain their original meaning. Tagged source Boxes
resolve the data address through OWNER and retain the emitted vtable word. -/
def decode (w : OWNER) (value : Data) : Option (Pointer × Pointer) :=
  match value with
  | .array [data,vtable] => do
    let d ← PV_THR2_OwnInitPointerCodec.decode data
    let v ← PV_THR2_OwnInitPointerCodec.decode vtable
    pure (d,v)
  | _ => sourceWords w value

def Relates (w : OWNER) (value : Data) (data vtable : Pointer) : Prop :=
  decode w value = some (data,vtable)
/-- The pinned symbol address is run-independent. This names the binary
linkage check; it is deliberately not assumed by a credited theorem. -/
def EmittedVtable115 (symbols : PV_THR2_OperatorSemantics_14119.Symbols)
    (binarySymbolAddress : Pointer) : Prop := symbols.vtable_115 = binarySymbolAddress

theorem bare (w : OWNER) (d v : Pointer) :
    Relates w (PV_THR2_OwnInitFieldCodec.callback d v) d v := by
  simp only [Relates,decode,PV_THR2_OwnInitFieldCodec.callback,
    PV_THR2_OwnInitPointerCodec.roundtrip,Option.bind_some,Bind.bind,Pure.pure]

/-- Exact f443 source reference,14119/14121 fat-pointer casts,612 Unique,
f458 Box constructor and14318/14541 casts. The registry binding is local
input here; ClosureBoxRegistry derives it from the actual allocation. -/
def callback (symbols : PV_THR2_OperatorSemantics_14119.Symbols) (p : Address) : Data :=
  PV_THR2_OperatorSemantics_14541.result (PV_THR2_OperatorSemantics_14318.result
    (PV_THR2_Box537Suffix13.boxed
      (PV_THR2_IntrinsicSemantics_UniqueNewUnchecked612.value
        (PV_THR2_OperatorSemantics_14121.result
          (PV_THR2_OperatorSemantics_14119.result symbols
            (PV_STX2_TypedReferences.reference p .null))))
      PV_THR2_Box458Prefix5.allocator))

theorem source (w : OWNER) (symbols : PV_THR2_OperatorSemantics_14119.Symbols)
    (p : Address) (d : Pointer) (binding : runtime w p = some d) :
    Relates w (callback symbols p) d symbols.vtable_115 := by
  change ((PV_STX2_TypedReferences.decode (PV_STX2_TypedReferences.reference p .null)) >>=
    fun pair => runtime w pair.1 >>= fun data =>
      PV_THR2_OwnInitPointerCodec.decode (PV_THR2_OperatorSemantics_14119.vtable_115 symbols) >>=
        fun vtable => some (data,vtable)) = _
  rw [PV_STX2_TypedReferences.roundtrip]
  simp only [Bind.bind,Option.bind_some,binding,PV_THR2_OperatorSemantics_14119.vtable_115,
    PV_THR2_OwnInitPointerCodec.roundtrip]
#print axioms bare
#print axioms source
end PV_THR2_BoxDynRepresentationBridge
