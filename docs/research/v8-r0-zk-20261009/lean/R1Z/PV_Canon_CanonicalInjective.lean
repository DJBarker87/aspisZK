import R1Z.PV_Canon_Carrier
import R1Z.ProverRwSuccessScalarInverseExact
set_option autoImplicit false
namespace R1Z.PV_Canon
open Aeneas Aeneas.Std
 theorem canonical_injective (x y : U32) (hx : M x) (hy : M y)
    (h : ProverCommitM31Ops48.decode x = ProverCommitM31Ops48.decode y) : x=y := by
  have val := congrArg ZMod.val h
  change x.val % 2147483647 = y.val % 2147483647 at val
  rw [Nat.mod_eq_of_lt hx,Nat.mod_eq_of_lt hy] at val
  exact UScalar.eq_of_val_eq val
#print axioms canonical_injective
end R1Z.PV_Canon
