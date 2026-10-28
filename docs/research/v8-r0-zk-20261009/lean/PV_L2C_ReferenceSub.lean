import PV_L2C_ReferenceArithmetic
set_option autoImplicit false
namespace PV_L2C_ReferenceSub
open Aeneas Aeneas.Std Result AspisR1ProverBalance9 PV_L2C_ReferenceArithmetic


theorem m31_sub (x y : U32) :
    aspis_core.field.M31.sub x y=ok (wrap (PV_L2C_M31.sub x.bv y.bv)) := by
  rw [PV_L2C_M31.sub,PV_L2C_M31.subtractP_branch]
  unfold aspis_core.field.M31.sub aspis_core.field.P
  change (if PV_L2C_M31.p≤(x.bv+BitVec.ofNat 32 PV_L2C_M31.p-y.bv).toNat then
    ok (wrap ((x.bv+BitVec.ofNat 32 PV_L2C_M31.p-y.bv)-BitVec.ofNat 32 PV_L2C_M31.p))
    else ok (wrap (x.bv+BitVec.ofNat 32 PV_L2C_M31.p-y.bv)))=
    ok (wrap (if PV_L2C_M31.p≤(x.bv+BitVec.ofNat 32 PV_L2C_M31.p-y.bv).toNat then
      (x.bv+BitVec.ofNat 32 PV_L2C_M31.p-y.bv)-BitVec.ofNat 32 PV_L2C_M31.p
      else x.bv+BitVec.ofNat 32 PV_L2C_M31.p-y.bv))
  split <;> simp_all
#print axioms m31_sub
end PV_L2C_ReferenceSub
