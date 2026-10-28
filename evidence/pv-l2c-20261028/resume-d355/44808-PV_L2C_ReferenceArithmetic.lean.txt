import AspisR1ProverBalance9.Funs
import PV_L2C_M31
set_option autoImplicit false
namespace PV_L2C_ReferenceArithmetic
open Aeneas Aeneas.Std Result AspisR1ProverBalance9

def wrap (x : PV_L2C_M31.word) : U32 := ⟨x⟩

/-- Actual extracted reference operation equals the checked native wrapping
kernel. No canonicality hypothesis is needed for this representation equality. -/
theorem m31_add (x y : U32) :
    aspis_core.field.M31.add x y=ok (wrap (PV_L2C_M31.add x.bv y.bv)) := by
  rw [PV_L2C_M31.add,PV_L2C_M31.subtractP_branch]
  unfold aspis_core.field.M31.add aspis_core.field.P
  change (if PV_L2C_M31.p≤(x.bv+y.bv).toNat then
    ok (wrap ((x.bv+y.bv)-BitVec.ofNat 32 PV_L2C_M31.p)) else ok (wrap (x.bv+y.bv)))=
    ok (wrap (if PV_L2C_M31.p≤(x.bv+y.bv).toNat then
      (x.bv+y.bv)-BitVec.ofNat 32 PV_L2C_M31.p else x.bv+y.bv))
  split <;> simp_all
#print axioms m31_add

end PV_L2C_ReferenceArithmetic
