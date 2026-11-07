import LIB_VLib
import RSL_TX1_094
set_option autoImplicit false
namespace LIB_VLibR4
/-- The rev3 gate at actual VL-star, from canonicalScan's SAME proof slice.
The full scan law retains its original proof-length domain. -/
theorem discharge : RSL.TX1_094.R4Discharge LIB_VLib.library := LIBC_CanonicalScan.r4_value
#print axioms discharge
end LIB_VLibR4
