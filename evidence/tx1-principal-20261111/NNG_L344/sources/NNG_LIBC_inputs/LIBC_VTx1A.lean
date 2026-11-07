import LIBC_ParseShape
import LIBC_CanonicalScan
import LIBC_AccNew
import LIBC_WeightsNew
import LIBC_Finish
set_option autoImplicit false
noncomputable section
namespace LIBC_VTx1A
abbrev parseShape := LIBC_ParseShape.child
abbrev canonicalScan := LIBC_CanonicalScan.child
abbrev accNew := LIBC_AccNew.child
abbrev weightsNew := LIBC_WeightsNew.child
abbrev finish := LIBC_Finish.child
/-- Rev3 source-derived caller clause, at the identical proof and y1 slice. -/
abbrev r4 := LIBC_CanonicalScan.r4_value
end LIBC_VTx1A
