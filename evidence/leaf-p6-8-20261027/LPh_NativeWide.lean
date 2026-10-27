import LPh_NativeLinear
set_option autoImplicit false
noncomputable section
namespace AspisR1.LPh.Native
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NE NQ)
open ExtractedMaskQM31Mul
abbrev QWords := (Nat×Nat)×(Nat×Nat)
def wideMulWords (x y : QWords×QWords) : QWords×QWords :=
  let ac := qmMulWords x.1 y.1
  let bd := qmMulWords x.2 y.2
  let cross := qmMulWords (qAddWords x.1 x.2) (qAddWords y.1 y.2)
  (qAddWords ac (qUWords bd),qSubWords (qSubWords cross ac) bd)

theorem wide_mul_expanded (x y : NE) (hx : FIo_WideValues.Canon x) (hy : FIo_WideValues.Canon y) :
    ∃ z, FIo_Native.aspis_core.field.wide_exact.WideExact.mul x y=ok z ∧
      FIo_WideValues.Canon z ∧ nativeEWords z=wideMulWords (nativeEWords x) (nativeEWords y) := by
  obtain ⟨a,ha,ca,va⟩ := qm_mul_expanded x.c0 y.c0 hx.1 hy.1
  obtain ⟨b,hb,cb,vb⟩ := qm_mul_expanded x.c1 y.c1 hx.2 hy.2
  obtain ⟨c,hc,cc,vc⟩ := qm_add_expanded x.c0 x.c1 hx.1 hx.2
  obtain ⟨d,hd,cd,vd⟩ := qm_add_expanded y.c0 y.c1 hy.1 hy.2
  obtain ⟨e,he,ce,ve⟩ := qm_mul_expanded c d cc cd
  obtain ⟨f,hf,cf,vf⟩ := by_r_expanded b.c1 cb.2
  have cu : FIo_QMValues.Canon (⟨f,b.c0⟩ : NQ) := ⟨cf,cb.1⟩
  have hu : FIo_Native.aspis_core.field.wide_exact.mul_u b=ok (⟨f,b.c0⟩ : NQ) := by
    simp only [FIo_Native.aspis_core.field.wide_exact.mul_u,hf,bind_tc_ok]
  obtain ⟨g,hg,cg,vg⟩ := qm_add_expanded a ⟨f,b.c0⟩ ca cu
  obtain ⟨h,hh,ch,vh⟩ := qm_sub_expanded e a ce ca
  obtain ⟨i,hi,ci,vi⟩ := qm_sub_expanded h b ch cb
  refine ⟨⟨g,i⟩,?_,⟨cg,ci⟩,?_⟩
  · simp only [FIo_Native.aspis_core.field.wide_exact.WideExact.mul,ha,hb,hc,hd,he,hu,hg,hh,hi,bind_tc_ok]
  · change (nativeQWords g,nativeQWords i)=_
    have vu : nativeQWords (⟨f,b.c0⟩ : NQ)=qUWords (nativeQWords b) := by
      change (nativeCWords f,nativeCWords b.c0)=(rWords (nativeCWords b.c1),nativeCWords b.c0)
      exact Prod.ext vf rfl
    rw [vg,vi,vh,ve,vc,vd,vu,va,vb]
    rfl
#print axioms wide_mul_expanded
end AspisR1.LPh.Native
end
