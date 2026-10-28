import NDO_JGb_DecodeInjective
import NDO_JGd_ExactWords
set_option autoImplicit false
namespace AspisR1.JGd_MainInjective
open FIp_SemanticArithmetic FIp_SemanticValues

theorem source (x y : MQ) (hx : Canon x) (hy : Canon y)
    (same : decode x=decode y) : x=y := by
  have h := JGb_DecodeInjective.source (FIq_Carriers.toQ x) (FIq_Carriers.toQ y) hx hy same
  simpa only [FIq_Carriers.q_roundtrip] using congrArg FIq_Carriers.fromQ h
#print axioms source
end AspisR1.JGd_MainInjective
