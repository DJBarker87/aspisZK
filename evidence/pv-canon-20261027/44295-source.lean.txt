import R1Z.PV_Canon_Carrier
import R1Z.PV_Join_ParseComplexCanonical5
set_option autoImplicit false
namespace R1Z.PV_Canon
open Aeneas Aeneas.Std Result ProverRwFull
 theorem parse_cm31 (bytes : Slice U8) (x : aspis_core.field.CM31)
    (h : ProverRwSuccessParserSource.aspis_core.field.CM31.from_le_bytes bytes = .ok (some x)) : C x :=
  PV_Join_ParseComplexCanonical5.complex bytes (some x) h x rfl
#print axioms parse_cm31
end R1Z.PV_Canon
