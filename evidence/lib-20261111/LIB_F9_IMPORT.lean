import LIB_BUNDLE_IMPORT
import LIB_ParseShape094
import LIB_FullInstances
set_option autoImplicit false
open RSL
#check (LIB_Instances.VL : VLib)
#check (LIB_Instances.P : PreparedNew LIB_Instances.VL)
#check (LIB_Instances.C : TX1_345.S1Lib LIB_Instances.VL)
#check (LIB_FullInstances.L : PoolLib)
#check (LIB_FullInstances.V0 : TX2_241.V2Lib)
#check (LIBB_PoolLib.values : NND_PoolValues.Values LIB_FullInstances.L)
#check (LIBB_V2Star.values : NND_Tx2Values.Values LIB_FullInstances.V0)
#check (LIBB_V2Star.gate : ∀ x, TX2_241.Dom064 LIB_FullInstances.V0 x →
 LIBB_ReturnFunctional.ReturnFunctional (LIB_FullInstances.V0.tx2auth x.1 x.2.1 x.2.2))
#check LIBB_V2Star.weak_identity
#check LIBB_V2Star.weak_exact
#check LIB_FullInstances.library
#check LIB_ParseShapeTotal.source
#check LIB_ParseShapeTotal.frozen_wrong_length
#check LIB_ParseShape094.width_not_required
#print axioms LIB_ParseShapeTotal.functional
#print axioms LIB_ParseShape094.empty_reference
