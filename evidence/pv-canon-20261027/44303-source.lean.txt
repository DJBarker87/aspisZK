import R1Z.PV_Canon_Carrier
import R1Z.ProverRwSuccessScalarInverseExact
set_option autoImplicit false
namespace R1Z.PV_Canon
open Aeneas Aeneas.Std
 theorem canonical_injective (x y : U32) (hx : M x) (hy : M y)
    (h : ProverCommitM31Ops48.decode x = ProverCommitM31Ops48.decode y) : x=y :=
  ProverRwSuccessScalarInverseExact.canonical_injective x y hx hy h
#print axioms canonical_injective
end R1Z.PV_Canon
