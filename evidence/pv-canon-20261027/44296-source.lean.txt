import R1Z.PV_Canon_Carrier
import R1Z.PV_Join_ParseQuarticCanonical5
set_option autoImplicit false
namespace R1Z.PV_Canon
open Aeneas Aeneas.Std Result ProverRwFull
 theorem parse_qm31 (bytes : Slice U8) (x : aspis_core.field.QM31)
    (h : ProverRwSuccessParserSource.aspis_core.field.QM31.from_le_bytes bytes = .ok (some x)) : Q x :=
  PV_Join_ParseQuarticCanonical5.quartic bytes (some x) h x rfl
#print axioms parse_qm31
end R1Z.PV_Canon
