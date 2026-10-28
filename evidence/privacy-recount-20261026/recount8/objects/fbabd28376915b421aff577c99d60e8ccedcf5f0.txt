import R1Z.PV_Src_Transport
import R1Z.PV_RunJoin_SourceEndpoint
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_InstalledTransport

/-- Exact row_call at the SAME fixed honest caller used by SourceEndpoint and
privacy_headline_deployed. This identifies the installed mathematical S2 row
map with srcid's extracted arithmetic reference. It does not identify an
uninterpreted native bitwise dictionary leaf with that reference. -/
theorem endpoint_row_call (j : Fin 1024) :
    (PhaseWireLog2Bin.honest PV_RunJoin_SourceEndpoint.input).transport j =
      PV_Src_Transport.row j :=
  (PV_Src_Transport.row_eq j).symm

theorem endpoint_transport :
    (PhaseWireLog2Bin.honest PV_RunJoin_SourceEndpoint.input).transport =
      PV_Src_Transport.transport := by
  apply Equiv.ext
  exact endpoint_row_call

#print axioms endpoint_row_call
#print axioms endpoint_transport
end R1Z.PV_RunJoin_InstalledTransport
