import R1Z.PV_OWNI_SuffixLoop
set_option autoImplicit false
namespace R1Z.PV_OWNI_ScannedResult
open Aeneas Aeneas.Std Result PV_OWNI_RawOps PV_OWNI_Scanner
/-- No assumed scan split or builder success: literal raw scanner, monadic
builder and ordered lookup/multiply/add consumer compose for every raw column. -/
theorem result (point column : List Q) (len:point.length=10) :
 PV_OWNI_RawConsumer.source point column (width point) (trailing point) (suffix point)=
 ok (PV_OWNI_RawConsumer.value point column (width point) (trailing point) (suffix point)) :=
 PV_OWNI_RawConsumer.result point column _ _ _ (split point len) (suffix_bound point)

#print axioms result
end R1Z.PV_OWNI_ScannedResult
