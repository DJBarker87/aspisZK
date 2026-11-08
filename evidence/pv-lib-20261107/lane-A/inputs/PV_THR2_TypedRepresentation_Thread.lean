import PV_THR2_OwnInitPointerCodec
set_option autoImplicit false
namespace PV_THR2_TypedRepresentation_Thread
open PV_STX2_Syntax PV_OWN2_Codec
/-- D798 explicit named SHAPE hypothesis for a delivered Thread value
(type58, Pin<Arc<Inner>>), conditional on amended translator acceptance.
NOT derived from PV_OWN2_ClientLayout: its pinned clauses record offsets only.
Recount14 obligation: extend the fc8808eb binary-structural check with a
Thread typed-value clause: every delivered Thread has one ELF64 pointer word.
No pointer validity, fixed value, allocation success or endpoint is asserted. -/
def Shape (value : Data) : Prop :=
  ∃ word : Pointer, value = PV_THR2_OwnInitPointerCodec.encode word
/-- Hypothesis: exactly the named Thread representation shape. -/
theorem represented (value : Data) (shapeThread : Shape value) :
    ∃ word : Pointer, value = PV_THR2_OwnInitPointerCodec.encode word := shapeThread
#print axioms represented
end PV_THR2_TypedRepresentation_Thread
