import NFS_AccumPart02
import NFP_ProductLaw
set_option autoImplicit false
namespace AspisR1.NIC_FieldStubs
open Aeneas Aeneas.Std Result NFN_LPi_FieldValues

/-- Exact total natural-value law paired with the M31 oracle. -/
theorem m31 (x y : U32) : ∃ z,
 FIo_Native.aspis_core.field.M31.mul x y=ok z ∧
 z.val=(x.val*y.val)%2147483647 ∧ z.val<2147483647 :=
 NFP_ProductLaw.emitted x y

theorem add (x y : NE) (hx : canonE x) (hy : canonE y) : ∃ z,
 FIo_Native.aspis_core.field.wide_exact.WideExact.add x y=ok z ∧
 canonE z ∧ ew z=(addQ (qw x.c0) (qw y.c0),addQ (qw x.c1) (qw y.c1)) := by
 obtain ⟨a,ha,ca,va⟩ := NFS_LPi_TowerValues.qm_add x.c0 y.c0 hx.1 hy.1
 obtain ⟨b,hb,cb,vb⟩ := NFS_LPi_TowerValues.qm_add x.c1 y.c1 hx.2 hy.2
 refine ⟨⟨a,b⟩,?_,⟨ca,cb⟩,Prod.ext va vb⟩
 simp only [FIo_Native.aspis_core.field.wide_exact.WideExact.add,ha,hb,bind_tc_ok]

theorem subtract (x y : NQ) (hx : canonQ x) (hy : canonQ y) : ∃ z,
 FIo_Native.aspis_core.field.QM31.sub x y=ok z ∧ canonQ z ∧ qw z=subQ (qw x) (qw y) :=
 NFS_LPi_TowerValues.qm_sub x y hx hy

theorem product (x y : NE) (hx : canonE x) (hy : canonE y) : ∃ z,
 FIo_Native.aspis_core.field.wide_exact.WideExact.mul x y=ok z ∧
 canonE z ∧ ew z=mulE (ew x) (ew y) := NFS_LPi_TowerValues.wide_mul x y hx hy

theorem scale (x : NE) (s : U32) : ∃ z,
 FIo_Native.aspis_core.field.wide_exact.WideExact.mul_m31 x s=ok z ∧
 canonE z ∧ ew z=(NFS_NBG_FieldDischarge.scaleQ (qw x.c0) (s.val%2147483647),
 NFS_NBG_FieldDischarge.scaleQ (qw x.c1) (s.val%2147483647)) :=
 NFS_NBG_FieldDischarge.wide_scale x s

#print axioms m31
#print axioms add
#print axioms subtract
#print axioms product
#print axioms scale
#print NFN_LPi_CMProduct.realWord
#print NFN_LPi_CMProduct.imagWord
end AspisR1.NIC_FieldStubs
