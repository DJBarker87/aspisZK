import NNG_InstallBase
import NFU_PrefixRecords
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Install
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Transport
open NMP_ResultTransport (outer inner outer_inverse inner_inverse)

def validatedRecord (p : r1_wire.Prefix) (row : U8) : Result (core.result.Result r1_wire.ValidatedRecord r1_wire.Error) :=
 outer (inner fromT14 fromT13) (AspisR1PublicPreparation.r1_wire.Prefix.validated_record (toT12 p) row)
theorem record_same (p : r1_wire.Prefix) (row : U8) :
 outer (inner toT14 toT13) (validatedRecord p row)=
 AspisR1PublicPreparation.r1_wire.Prefix.validated_record (toT12 p) row := by
 apply outer_inverse
 intro r
 exact inner_inverse fromT14 toT14 fromT13 toT13 fromT14_inverse fromT13_inverse r
/-- CLOSED141 installed at the SAME original Prefix and row, all Results. -/
theorem record_source (p : r1_wire.Prefix) (row : U8) :
 outer (inner toT14 toT13) (validatedRecord p row)=
 NFU_PrefixRecords.token row (NFU_PrefixRecords.selected (toT12 p) row) :=
 (record_same p row).trans (NFU_PrefixRecords.validated_record (toT12 p) row)
#print axioms record_same
#print axioms record_source
end AspisR1.NNG_Install
