import R1Z.PV_CBL_FallbackScalar
open Aeneas Aeneas.Std
namespace R1Z.PV_CBL_FallbackAddAlgebra
set_option autoImplicit false
theorem comm (a b : U32) : U32.wrapping_add a b = U32.wrapping_add b a := by
  apply U32.bv_eq_imp_eq
  change a.bv+b.bv=b.bv+a.bv
  exact BitVec.add_comm _ _
theorem assoc (a b c : U32) :
    U32.wrapping_add (U32.wrapping_add a b) c = U32.wrapping_add a (U32.wrapping_add b c) := by
  apply U32.bv_eq_imp_eq
  change (a.bv+b.bv)+c.bv=a.bv+(b.bv+c.bv)
  exact BitVec.add_assoc _ _ _
theorem reverse4 (a b c d : U32) :
    U32.wrapping_add (U32.wrapping_add (U32.wrapping_add a b) c) d =
    U32.wrapping_add (U32.wrapping_add (U32.wrapping_add d c) b) a := by
  apply U32.bv_eq_imp_eq
  change ((a.bv+b.bv)+c.bv)+d.bv=((d.bv+c.bv)+b.bv)+a.bv
  calc
    ((a.bv+b.bv)+c.bv)+d.bv = d.bv+(c.bv+(a.bv+b.bv)) := by
      rw [BitVec.add_comm _ d.bv,BitVec.add_comm (a.bv+b.bv) c.bv]
    _ = (d.bv+c.bv)+(a.bv+b.bv) := (BitVec.add_assoc _ _ _).symm
    _ = (d.bv+c.bv)+(b.bv+a.bv) := by rw [BitVec.add_comm a.bv b.bv]
    _ = ((d.bv+c.bv)+b.bv)+a.bv := (BitVec.add_assoc _ _ _).symm
#print axioms comm
#print axioms assoc
#print axioms reverse4
end R1Z.PV_CBL_FallbackAddAlgebra
