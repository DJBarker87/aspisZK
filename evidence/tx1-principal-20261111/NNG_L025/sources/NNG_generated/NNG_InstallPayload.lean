import NNG_InstallBase
import NGX_Payload
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Install
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Transport
open NMP_ResultTransport (outer inner outer_inverse inner_inverse)

def payload (p : r1_wire.Prefix) (row : U8) :=
 outer (inner id fromT13) (AspisR1PublicPreparation.FinishModel.payload (toT12 p) row)
theorem payload_same (p : r1_wire.Prefix) (row : U8) :
 outer (inner id toT13) (payload p row)=
 AspisR1PublicPreparation.FinishModel.payload (toT12 p) row := by
 apply outer_inverse
 intro r
 exact inner_inverse id id fromT13 toT13 (fun _ => rfl) fromT13_inverse r
/-- CLOSED139 installed at the SAME original Prefix and row. Bad tail indices
retain their panic Result; no accepted-payload assumption is introduced. -/
theorem payload_source (p : r1_wire.Prefix) (row : U8) :
 outer (inner id toT13) (payload p row)=
 NGX_Payload.computation (NFU_PrefixRecords.selected (toT12 p) row) :=
 (payload_same p row).trans (NGX_Payload.source (toT12 p) row)
#print axioms payload_same
#print axioms payload_source
end AspisR1.NNG_Install
