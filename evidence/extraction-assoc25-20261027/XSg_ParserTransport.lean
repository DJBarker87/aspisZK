import XSg_OldDriver
import XSc_ParseDriver
open Aeneas Aeneas.Std Result XRn_Join_Release
open XRo_Join_Carriers XRo_Join_ResultTransport
set_option autoImplicit false
namespace XSg_ParserTransport
/-- COMPLETE old/cohort parser association on arbitrary bytes, with no
validator callback premise. Header, all27 records, finish, errors and carriers
are the actual literal programs on both sides. -/
theorem source (bytes : Slice U8) :
 mapR (inner XSe_ParseFinish.pre XRu_ParserShapes.error) (r1_wire.Prefix.parse bytes)=
 AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes := by
 rw [XSc_ParseDriver.source,XSg_OldDriver.source]
 unfold XRz_ParseFold.parse XSg_OldDriver.parse
 split
 · rfl
 · simp only [mapR_bind]
   congr 1
   funext s
   congr 1
   funext root
   cases root with
   | Err e => rfl
   | Ok root => exact XSe_ParseFinish.driver bytes root (.Ok ([],32#usize))
#print axioms source
end XSg_ParserTransport
