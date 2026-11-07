import LIB_BUNDLE_IMPORT
import LIBB_COMBINED_IMPORT
import LIBB_V2Lib
set_option autoImplicit false
-- Focused coherent cached closure. No I.f064 installation or full-Obs
-- Functional assertion is smuggled into this import check.
#check (LIBB_V2Lib.library : RSL.TX2_241.V2Lib)
#check (LIBB_V2Lib.values : NND_Tx2Values.Values LIBB_V2Lib.library)
#check LIBB_Tx2Auth.native
#check LIBB_Tx2Auth.returns
#check LIBB_Tx2Auth.writeFree
#check LIBB_Tx2Auth.resolved_functional
#check LIBB_V2Lib.returned_gate
#check LIBB_V2Lib.weak_exact
#check LIBB_V2Lib.canonical_identity
#check LIBB_V2Lib.weak_identity
#check (LIB_Instances.VL : RSL.VLib)
#check (LIB_Instances.P : RSL.PreparedNew LIB_Instances.VL)
#check (LIB_Instances.C : RSL.TX1_345.S1Lib LIB_Instances.VL)
