import XRz_RecordTransport
open Aeneas Aeneas.Std Result XRn_Join_Release XRo_Join_Carriers
set_option autoImplicit false
namespace XSc_RecordFieldTypes
abbrev OQ := AspisR1PrefixAggregateParser.field.QM31
abbrev OW := AspisR1PrefixAggregateParser.field.wide_exact.WideExact

def q (x : OQ) : AspisR1PublicPreparation.aspis_core.field.QM31 :=
 ⟨⟨x.c0.a,x.c0.b⟩,⟨x.c1.a,x.c1.b⟩⟩
def wide (x : OW) : XRn_Join_Wide := ⟨q x.c0,q x.c1⟩
#check AspisR1PrefixAggregateParser.field.wide_exact.WideExact.from_limbs
#check XRn_Join_Release.aspis_core.field.wide_exact.WideExact.from_limbs
#print XRn_Join_Wide
#print Aeneas.Std.core.num.U32.from_le_bytes
end XSc_RecordFieldTypes
