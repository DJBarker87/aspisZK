import R1Z.PV_OWNK_TowerCanon
import R1Z.PV_OWNK_FieldScalar
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_OWNK_CMDecode
open Aeneas Aeneas.Std
open PV_OWNK_TowerCanon
abbrev F := PV_OWNK_FieldScalar.F
abbrev E := AspisV8R15.ExactTowerBase.CM31Exact
abbrev M := PV_OWNK_ScalarOps.M
abbrev ds := PV_OWNK_FieldScalar.decode
def decode (x : C) : E := ⟨ds x.a,ds x.b⟩

theorem add (x y : C) (hx : CC x) (hy : CC y) :
 decode (PV_B2_FieldValue.aspis_core.field.CM31.add x y) = decode x + decode y := by
 apply QuadraticAlgebra.ext
 · exact PV_OWNK_FieldScalar.add _ _ hx.1 hy.1
 · exact PV_OWNK_FieldScalar.add _ _ hx.2 hy.2

theorem sub (x y : C) (hx : CC x) (hy : CC y) :
 decode (PV_B2_FieldValue.aspis_core.field.CM31.sub x y) = decode x - decode y := by
 apply QuadraticAlgebra.ext
 · exact PV_OWNK_FieldScalar.sub _ _ hx.1 hy.1
 · exact PV_OWNK_FieldScalar.sub _ _ hx.2 hy.2

def cross (x y : C) : U64 :=
 U64.wrapping_mul
  (U64.wrapping_add (core.convert.num.FromU64U32.from x.a) (core.convert.num.FromU64U32.from x.b))
  (U64.wrapping_add (core.convert.num.FromU64U32.from y.a) (core.convert.num.FromU64U32.from y.b))

theorem cross_val (x y : C) (hx : CC x) (hy : CC y) :
 (cross x y).val = (x.a.val+x.b.val)*(y.a.val+y.b.val) := by
 have cast_val (a : U32) : (core.convert.num.FromU64U32.from a).val = a.val := by
  change (UScalar.cast .U64 a).val = a.val
  rw [UScalar.cast_val_eq]
  exact Nat.mod_eq_of_lt (by have h : a.val < 4294967296 := a.hBounds; change a.val < 18446744073709551616; omega)
 have ha : x.a.val+x.b.val < 4294967296 := by obtain ⟨ha,hb⟩:=hx; unfold PV_OWNK_ScalarOps.Canon at ha hb; omega
 have hb : y.a.val+y.b.val < 4294967296 := by obtain ⟨ha,hb⟩:=hy; unfold PV_OWNK_ScalarOps.Canon at ha hb; omega
 unfold cross
 rw [U64.wrapping_mul_val_eq,U64.wrapping_add_val_eq,U64.wrapping_add_val_eq,
  cast_val,cast_val,cast_val,cast_val,UScalar.size]
 change ((x.a.val+x.b.val)%18446744073709551616 *
  ((y.a.val+y.b.val)%18446744073709551616))%18446744073709551616 = _
 rw [Nat.mod_eq_of_lt (show x.a.val+x.b.val < 18446744073709551616 by omega),
  Nat.mod_eq_of_lt (show y.a.val+y.b.val < 18446744073709551616 by omega)]
 exact Nat.mod_eq_of_lt (by nlinarith)

theorem mul (x y : C) (hx : CC x) (hy : CC y) :
 decode (PV_B2_FieldValue.aspis_core.field.CM31.mul x y) = decode x * decode y := by
 have h0 := PV_OWNK_ScalarOps.mul_canon x.a y.a
 have h1 := PV_OWNK_ScalarOps.mul_canon x.b y.b
 have h2 := PV_OWNK_ScalarOps.reduce_canon (cross x y)
 apply QuadraticAlgebra.ext
 · change ds (PV_B2_FieldValue.aspis_core.field.M31.sub (PV_B2_FieldValue.aspis_core.field.M31.mul x.a y.a) (PV_B2_FieldValue.aspis_core.field.M31.mul x.b y.b)) = _
   rw [PV_OWNK_FieldScalar.sub _ _ h0 h1,PV_OWNK_FieldScalar.mul,PV_OWNK_FieldScalar.mul]
   simp only [QuadraticAlgebra.re_mul,decode]
   ring
 · change ds (PV_B2_FieldValue.aspis_core.field.M31.sub (PV_B2_FieldValue.aspis_core.field.M31.sub (PV_B2_FieldValue.aspis_core.field.M31.reduce_u64 (cross x y)) (PV_B2_FieldValue.aspis_core.field.M31.mul x.a y.a)) (PV_B2_FieldValue.aspis_core.field.M31.mul x.b y.b)) = _
   rw [PV_OWNK_FieldScalar.sub _ _ (PV_OWNK_ScalarOps.sub_canon _ _ h2 h0) h1,
    PV_OWNK_FieldScalar.sub _ _ h2 h0,PV_OWNK_FieldScalar.reduce,
    cross_val x y hx hy, Nat.cast_mul,Nat.cast_add,Nat.cast_add,
    PV_OWNK_FieldScalar.mul,PV_OWNK_FieldScalar.mul]
   simp only [QuadraticAlgebra.im_mul,decode,PV_OWNK_FieldScalar.decode]
   ring

theorem mul_by_r (x : C) (hx : CC x) :
 decode (PV_B2_FieldValue.aspis_core.field.mul_by_r x) =
 AspisV8R15.ExactTowerBase.qm31R * decode x := by
 apply QuadraticAlgebra.ext
 · change ds (PV_B2_FieldValue.aspis_core.field.M31.sub (PV_B2_FieldValue.aspis_core.field.M31.double x.a) x.b) = _
   rw [PV_OWNK_FieldScalar.sub _ _ (PV_OWNK_ScalarOps.double_canon _ hx.1) hx.2,
    PV_OWNK_FieldScalar.double _ hx.1]
   simp only [QuadraticAlgebra.re_mul,decode,AspisV8R15.ExactTowerBase.qm31R]
   ring
 · change ds (PV_B2_FieldValue.aspis_core.field.M31.add x.a (PV_B2_FieldValue.aspis_core.field.M31.double x.b)) = _
   rw [PV_OWNK_FieldScalar.add _ _ hx.1 (PV_OWNK_ScalarOps.double_canon _ hx.2),
    PV_OWNK_FieldScalar.double _ hx.2]
   simp only [QuadraticAlgebra.im_mul,decode,AspisV8R15.ExactTowerBase.qm31R]
   ring

#print axioms add
#print axioms sub
#print axioms cross_val
#print axioms mul
#print axioms mul_by_r
end R1Z.PV_OWNK_CMDecode
