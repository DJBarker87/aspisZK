import PV_THR2_OwnInitFieldCodec
set_option autoImplicit false
namespace PV_THR2_TypedRepresentation_BoxDynFnOnce
open PV_STX2_Syntax PV_OWN2_Codec
/-- D798 explicit named SHAPE hypothesis for a delivered Box<dyn FnOnce()+Send>
value, conditional on amended translator acceptance. NOT derived from the
pinned PV_OWN2_ClientLayout offsets. Recount14 obligation: extend the fc8808eb
binary-structural check with the typed-value clause that this Box is represented
by an ELF64 data word and vtable word. No payload value or validity is fixed. -/
def Shape (value : Data) : Prop :=
  ∃ data vtable : Pointer, value = PV_THR2_OwnInitFieldCodec.callback data vtable
/-- Hypothesis: exactly the named fat callback representation shape. -/
theorem represented (value : Data) (shapeBoxDynFnOnce : Shape value) :
    ∃ data vtable : Pointer, value = PV_THR2_OwnInitFieldCodec.callback data vtable :=
  shapeBoxDynFnOnce
#print axioms represented
end PV_THR2_TypedRepresentation_BoxDynFnOnce
