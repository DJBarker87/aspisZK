import LPh_NativeScalar
import RPt_FIo_WideMulValues
set_option autoImplicit false
noncomputable section
namespace AspisR1.LPh.Native
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NC NQ NE cm qm wide)
open AspisR1CurrentWide.Proof

private theorem add_total (x y : U32) : ∃ z, FIo_Native.aspis_core.field.M31.add x y=ok z := by
  unfold FIo_Native.aspis_core.field.M31.add
  simp only [lift,bind_tc_ok]
  split <;> exact ⟨_,rfl⟩
private theorem sub_total (x y : U32) : ∃ z, FIo_Native.aspis_core.field.M31.sub x y=ok z := by
  unfold FIo_Native.aspis_core.field.M31.sub
  simp only [lift,bind_tc_ok]
  split <;> exact ⟨_,rfl⟩
private theorem reduce_total (x : U64) : ∃ z, FIo_Native.aspis_core.field.M31.reduce_u64 x=ok z := by
  unfold FIo_Native.aspis_core.field.M31.reduce_u64 FIo_Native.aspis_core.field.reduce_u64
  simp only [lift,bind_tc_ok]
  split <;> exact ⟨_,rfl⟩

theorem cm_add_total (x y : NC) : ∃ z, FIo_Native.aspis_core.field.CM31.add x y=ok z := by
  obtain ⟨a,ha⟩ := add_total x.a y.a
  obtain ⟨b,hb⟩ := add_total x.b y.b
  exact ⟨⟨a,b⟩,by simp only [FIo_Native.aspis_core.field.CM31.add,ha,hb,bind_tc_ok]⟩
theorem cm_sub_total (x y : NC) : ∃ z, FIo_Native.aspis_core.field.CM31.sub x y=ok z := by
  obtain ⟨a,ha⟩ := sub_total x.a y.a
  obtain ⟨b,hb⟩ := sub_total x.b y.b
  exact ⟨⟨a,b⟩,by simp only [FIo_Native.aspis_core.field.CM31.sub,ha,hb,bind_tc_ok]⟩

theorem by_r_total (x : NC) : ∃ z, FIo_Native.aspis_core.field.mul_by_r x=ok z := by
  obtain ⟨a,ha⟩ := add_total x.a x.a
  obtain ⟨b,hb⟩ := sub_total a x.b
  obtain ⟨c,hc⟩ := add_total x.b x.b
  obtain ⟨d,hd⟩ := add_total x.a c
  exact ⟨⟨b,d⟩,by simp only [FIo_Native.aspis_core.field.mul_by_r,FIo_Native.aspis_core.field.M31.double,ha,hb,hc,hd,bind_tc_ok]⟩

theorem cm_mul_total (x y : NC) : ∃ z, FIo_Native.aspis_core.field.CM31.mul x y=ok z := by
  obtain ⟨a,ha,_,_⟩ := m31_value x.a y.a
  obtain ⟨b,hb,_,_⟩ := m31_value x.b y.b
  obtain ⟨c,hc⟩ := reduce_total (FIo_CMProduct.cross x y)
  obtain ⟨d,hd⟩ := sub_total a b
  obtain ⟨e,he⟩ := sub_total c a
  obtain ⟨f,hf⟩ := sub_total e b
  refine ⟨⟨d,f⟩,?_⟩
  simp only [FIo_Native.aspis_core.field.CM31.mul,ha,hb,lift,bind_tc_ok]
  change (do
    let c ← FIo_Native.aspis_core.field.M31.reduce_u64 (FIo_CMProduct.cross x y)
    let a ← FIo_Native.aspis_core.field.M31.sub a b
    let b ← FIo_Native.aspis_core.field.M31.sub c _
    let b ← FIo_Native.aspis_core.field.M31.sub b _
    ok (⟨a,b⟩ : NC)) = _
  simp only [hc,hd,he,hf,bind_tc_ok]

theorem qm_add_total (x y : NQ) : ∃ z, FIo_Native.aspis_core.field.QM31.add x y=ok z := by
  obtain ⟨a,ha⟩ := cm_add_total x.c0 y.c0
  obtain ⟨b,hb⟩ := cm_add_total x.c1 y.c1
  exact ⟨⟨a,b⟩,by simp only [FIo_Native.aspis_core.field.QM31.add,ha,hb,bind_tc_ok]⟩
theorem qm_sub_total (x y : NQ) : ∃ z, FIo_Native.aspis_core.field.QM31.sub x y=ok z := by
  obtain ⟨a,ha⟩ := cm_sub_total x.c0 y.c0
  obtain ⟨b,hb⟩ := cm_sub_total x.c1 y.c1
  exact ⟨⟨a,b⟩,by simp only [FIo_Native.aspis_core.field.QM31.sub,ha,hb,bind_tc_ok]⟩

theorem qm_mul_total (x y : NQ) : ∃ z, FIo_Native.aspis_core.field.QM31.mul x y=ok z := by
  obtain ⟨a,ha⟩ := cm_mul_total x.c0 y.c0
  obtain ⟨b,hb⟩ := cm_mul_total x.c1 y.c1
  obtain ⟨c,hc⟩ := cm_add_total x.c0 x.c1
  obtain ⟨d,hd⟩ := cm_add_total y.c0 y.c1
  obtain ⟨e,he⟩ := cm_mul_total c d
  obtain ⟨f,hf⟩ := by_r_total b
  obtain ⟨g,hg⟩ := cm_add_total a f
  obtain ⟨h,hh⟩ := cm_sub_total e a
  obtain ⟨i,hi⟩ := cm_sub_total h b
  exact ⟨⟨g,i⟩,by simp only [FIo_Native.aspis_core.field.QM31.mul,ha,hb,hc,hd,he,hf,hg,hh,hi,bind_tc_ok]⟩

theorem wide_mul_total (x y : NE) : ∃ z, FIo_Native.aspis_core.field.wide_exact.WideExact.mul x y=ok z := by
  obtain ⟨a,ha⟩ := qm_mul_total x.c0 y.c0
  obtain ⟨b,hb⟩ := qm_mul_total x.c1 y.c1
  obtain ⟨c,hc⟩ := qm_add_total x.c0 x.c1
  obtain ⟨d,hd⟩ := qm_add_total y.c0 y.c1
  obtain ⟨e,he⟩ := qm_mul_total c d
  obtain ⟨f,hf⟩ := by_r_total b.c1
  have hu : FIo_Native.aspis_core.field.wide_exact.mul_u b=ok (⟨f,b.c0⟩ : NQ) := by
    simp only [FIo_Native.aspis_core.field.wide_exact.mul_u,hf,bind_tc_ok]
  obtain ⟨g,hg⟩ := qm_add_total a ⟨f,b.c0⟩
  obtain ⟨h,hh⟩ := qm_sub_total e a
  obtain ⟨i,hi⟩ := qm_sub_total h b
  exact ⟨⟨g,i⟩,by simp only [FIo_Native.aspis_core.field.wide_exact.WideExact.mul,ha,hb,hc,hd,he,hu,hg,hh,hi,bind_tc_ok]⟩

theorem wide_mul_value (x y : NE) (hx : FIo_WideValues.Canon x) (hy : FIo_WideValues.Canon y) :
    ∃ z, FIo_Native.aspis_core.field.wide_exact.WideExact.mul x y=ok z ∧
      FIo_WideValues.Canon z ∧ decodeWide (wide z)=decodeWide (wide x)*decodeWide (wide y) := by
  obtain ⟨z,hz⟩ := wide_mul_total x y
  exact ⟨z,hz,FIo_WideMulValues.mul x y z hx hy hz⟩

#print axioms cm_add_total
#print axioms cm_sub_total
#print axioms by_r_total
#print axioms cm_mul_total
#print axioms qm_add_total
#print axioms qm_sub_total
#print axioms qm_mul_total
#print axioms wide_mul_total
#print axioms wide_mul_value
end AspisR1.LPh.Native
end
