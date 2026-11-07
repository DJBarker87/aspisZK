import LIBB_RESUME_IMPORT
import LIBB_V2Star
set_option autoImplicit false
set_option pp.proofs false
-- Final focused coherent import: ledger25, merged TX1 bundle and full TX2 V0-star.
#check (LIBB_V2Star.library : RSL.TX2_241.V2Lib)
#check (LIBB_V2Star.values : NND_Tx2Values.Values LIBB_V2Star.library)
#check (LIBB_V2Star.gate : ∀ x, RSL.TX2_241.Dom064 LIBB_V2Star.library x →
 LIBB_ReturnFunctional.ReturnFunctional (LIBB_V2Star.library.tx2auth x.1 x.2.1 x.2.2))
#check LIBB_Tx2Auth.native
#check LIBB_V2Star.weak_identity
#check LIBB_V2Star.weak_exact
#check (LIB_Instances.VL : RSL.VLib)
#check (LIB_Instances.P : RSL.PreparedNew LIB_Instances.VL)
#check (LIB_Instances.C : RSL.TX1_345.S1Lib LIB_Instances.VL)
#print LIBB_ReturnFunctional.ReturnFunctional
#print LIBB_Tx2AuthGate.returnFunctional
#print LIBB_Tx2AuthGate.returned_resolved
#print LIBB_V2Star.gate
#print LIBB_V2Star.library
#print LIBB_V2Star.weak
#print axioms LIBB_V2Star.gate
