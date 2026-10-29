import R1Z.PV_OWND_InitialCheck
import R1Z.PV_OWND_SourceShape
set_option autoImplicit false
attribute [local irreducible] R1Z.PV_OWND_EndpointCounter.check R1Z.PV_OWND_LegacySource.links
namespace R1Z.PV_OWND_CheckSource
open PV_OWN_Heap PV_OWN_Link PV_OWN_Bytes PV_OWND_EndpointCounter PV_OWND_InitialCheck
/-- The check input is derived from the actual initialized full-Link values.
The scalar check is not declared native until the two stack arrays are bound. -/
theorem scalar_input (m : Memory) (t : Token) (owner : Nat) (payload : Nat → Link → Bytes) :
 checks (PV_OWND_ActualBytes.initialized m t owner payload)=
 match check PV_OWND_LegacySource.links (fun _=>0) (fun _=>0) with
 | .error (.endpointCapacity row) => .error (.endpoint row)
 | .ok _ => .ok () := by
 simp only [checks,PV_OWND_SourceShape.no_shape_error,ite_false,PV_OWND_ActualItems.source]
 rfl
#print axioms scalar_input
end R1Z.PV_OWND_CheckSource
