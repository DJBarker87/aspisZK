import LPh_ExpandedC
set_option autoImplicit false
noncomputable section
namespace AspisR1.LPh.Native
open Aeneas Aeneas.Std Result
open AspisR1CurrentWide.Proof
open FIo_FieldBridge (NC NQ)
open ExtractedMaskQM31Mul

theorem add_value (x y : U32) (hx : x.val<2147483647) (hy : y.val<2147483647) :
    ∃ z, FIo_Native.aspis_core.field.M31.add x y=ok z ∧
      z.val=(x.val+y.val)%2147483647 ∧ z.val<2147483647 := by
  rw [FIo_M31Bridge.add x y hx hy,m31_add_same]
  exact ExtractedCurrentM31AddSub.current_add_mod x y hx hy

theorem sub_value (x y : U32) (hx : x.val<2147483647) (hy : y.val<2147483647) :
    ∃ z, FIo_Native.aspis_core.field.M31.sub x y=ok z ∧
      z.val=(x.val+2147483647-y.val)%2147483647 ∧ z.val<2147483647 := by
  rw [FIo_M31SubBridge.sub x y hx hy,m31_sub_same]
  exact ExtractedCurrentM31AddSub.current_sub_mod x y hx hy

theorem cm_add_expanded (x y : NC) (hx : FIo_CMValues.Canon x) (hy : FIo_CMValues.Canon y) :
    ∃ z, FIo_Native.aspis_core.field.CM31.add x y=ok z ∧ FIo_CMValues.Canon z ∧
      nativeCWords z=addWords (nativeCWords x) (nativeCWords y) := by
  obtain ⟨a,ha,va,ca⟩ := add_value x.a y.a hx.1 hy.1
  obtain ⟨b,hb,vb,cb⟩ := add_value x.b y.b hx.2 hy.2
  exact ⟨⟨a,b⟩,by simp only [FIo_Native.aspis_core.field.CM31.add,ha,hb,bind_tc_ok],⟨ca,cb⟩,Prod.ext va vb⟩

theorem cm_sub_expanded (x y : NC) (hx : FIo_CMValues.Canon x) (hy : FIo_CMValues.Canon y) :
    ∃ z, FIo_Native.aspis_core.field.CM31.sub x y=ok z ∧ FIo_CMValues.Canon z ∧
      nativeCWords z=subWords (nativeCWords x) (nativeCWords y) := by
  obtain ⟨a,ha,va,ca⟩ := sub_value x.a y.a hx.1 hy.1
  obtain ⟨b,hb,vb,cb⟩ := sub_value x.b y.b hx.2 hy.2
  exact ⟨⟨a,b⟩,by simp only [FIo_Native.aspis_core.field.CM31.sub,ha,hb,bind_tc_ok],⟨ca,cb⟩,Prod.ext va vb⟩

theorem by_r_expanded (x : NC) (hx : FIo_CMValues.Canon x) :
    ∃ z, FIo_Native.aspis_core.field.mul_by_r x=ok z ∧ FIo_CMValues.Canon z ∧
      nativeCWords z=rWords (nativeCWords x) := by
  obtain ⟨a,ha,va,ca⟩ := add_value x.a x.a hx.1 hx.1
  obtain ⟨b,hb,vb,cb⟩ := sub_value a x.b ca hx.2
  obtain ⟨c,hc,vc,cc⟩ := add_value x.b x.b hx.2 hx.2
  obtain ⟨d,hd,vd,cd⟩ := add_value x.a c hx.1 cc
  refine ⟨⟨b,d⟩,?_,⟨cb,cd⟩,?_⟩
  · simp only [FIo_Native.aspis_core.field.mul_by_r,FIo_Native.aspis_core.field.M31.double,ha,hb,hc,hd,bind_tc_ok]
  · change (b.val,d.val)=rWords (nativeCWords x)
    simp only [rWords,nativeCWords]
    exact Prod.ext (by simpa only [va] using vb) (by simpa only [vc] using vd)

def qAddWords (x y : (Nat×Nat)×(Nat×Nat)) := (addWords x.1 y.1,addWords x.2 y.2)
def qSubWords (x y : (Nat×Nat)×(Nat×Nat)) := (subWords x.1 y.1,subWords x.2 y.2)
def qUWords (x : (Nat×Nat)×(Nat×Nat)) := (rWords x.2,x.1)

theorem qm_add_expanded (x y : NQ) (hx : FIo_QMValues.Canon x) (hy : FIo_QMValues.Canon y) :
    ∃ z, FIo_Native.aspis_core.field.QM31.add x y=ok z ∧ FIo_QMValues.Canon z ∧
      nativeQWords z=qAddWords (nativeQWords x) (nativeQWords y) := by
  obtain ⟨a,ha,ca,va⟩ := cm_add_expanded x.c0 y.c0 hx.1 hy.1
  obtain ⟨b,hb,cb,vb⟩ := cm_add_expanded x.c1 y.c1 hx.2 hy.2
  exact ⟨⟨a,b⟩,by simp only [FIo_Native.aspis_core.field.QM31.add,ha,hb,bind_tc_ok],⟨ca,cb⟩,Prod.ext va vb⟩

theorem qm_sub_expanded (x y : NQ) (hx : FIo_QMValues.Canon x) (hy : FIo_QMValues.Canon y) :
    ∃ z, FIo_Native.aspis_core.field.QM31.sub x y=ok z ∧ FIo_QMValues.Canon z ∧
      nativeQWords z=qSubWords (nativeQWords x) (nativeQWords y) := by
  obtain ⟨a,ha,ca,va⟩ := cm_sub_expanded x.c0 y.c0 hx.1 hy.1
  obtain ⟨b,hb,cb,vb⟩ := cm_sub_expanded x.c1 y.c1 hx.2 hy.2
  exact ⟨⟨a,b⟩,by simp only [FIo_Native.aspis_core.field.QM31.sub,ha,hb,bind_tc_ok],⟨ca,cb⟩,Prod.ext va vb⟩

#print axioms add_value
#print axioms sub_value
#print axioms cm_add_expanded
#print axioms cm_sub_expanded
#print axioms by_r_expanded
#print axioms qm_add_expanded
#print axioms qm_sub_expanded
end AspisR1.LPh.Native
end
