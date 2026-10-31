import NEB_QMCalls
set_option autoImplicit false
namespace NEB_WideCalls
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues

theorem multiply (x y : NE) (hx : canonE x) (hy : canonE y) :
    ∃ ac bd a b cross r lo diff hi : NQ,
      FIo_Native.aspis_core.field.QM31.mul x.c0 y.c0 = ok ac ∧ canonQ ac ∧
      FIo_Native.aspis_core.field.QM31.mul x.c1 y.c1 = ok bd ∧ canonQ bd ∧
      FIo_Native.aspis_core.field.QM31.add x.c0 x.c1 = ok a ∧ canonQ a ∧
      FIo_Native.aspis_core.field.QM31.add y.c0 y.c1 = ok b ∧ canonQ b ∧
      FIo_Native.aspis_core.field.QM31.mul a b = ok cross ∧ canonQ cross ∧
      FIo_Native.aspis_core.field.wide_exact.mul_u bd = ok r ∧ canonQ r ∧
      FIo_Native.aspis_core.field.QM31.add ac r = ok lo ∧ canonQ lo ∧
      FIo_Native.aspis_core.field.QM31.sub cross ac = ok diff ∧ canonQ diff ∧
      FIo_Native.aspis_core.field.QM31.sub diff bd = ok hi ∧ canonQ hi ∧
      FIo_Native.aspis_core.field.wide_exact.WideExact.mul x y = ok ⟨lo,hi⟩ := by
  obtain ⟨ac,hac,cac,_⟩ := LPi_TowerValues.qm_mul x.c0 y.c0 hx.1 hy.1
  obtain ⟨bd,hbd,cbd,_⟩ := LPi_TowerValues.qm_mul x.c1 y.c1 hx.2 hy.2
  obtain ⟨a,ha,ca,_⟩ := LPi_TowerValues.qm_add x.c0 x.c1 hx.1 hx.2
  obtain ⟨b,hb,cb,_⟩ := LPi_TowerValues.qm_add y.c0 y.c1 hy.1 hy.2
  obtain ⟨cross,hcross,ccross,_⟩ := LPi_TowerValues.qm_mul a b ca cb
  obtain ⟨r,hr,cr,_⟩ := LPi_TowerValues.mul_u bd cbd
  obtain ⟨lo,hlo,clo,_⟩ := LPi_TowerValues.qm_add ac r cac cr
  obtain ⟨diff,hdiff,cdiff,_⟩ := LPi_TowerValues.qm_sub cross ac ccross cac
  obtain ⟨hi,hhi,chi,_⟩ := LPi_TowerValues.qm_sub diff bd cdiff cbd
  exact ⟨ac,bd,a,b,cross,r,lo,diff,hi,hac,cac,hbd,cbd,ha,ca,hb,cb,
    hcross,ccross,hr,cr,hlo,clo,hdiff,cdiff,hhi,chi,by
      simp only [FIo_Native.aspis_core.field.wide_exact.WideExact.mul,hac,hbd,ha,hb,hcross,hr,hlo,hdiff,hhi,bind_tc_ok]⟩

theorem mixed (x : NE) (y : NQ) (hx : canonE x) :
    ∃ rhs a b,
      FIo_Native.aspis_core.field.wide_exact.canonical_qm31 y = ok rhs ∧ canonQ rhs ∧
      FIo_Native.aspis_core.field.QM31.mul x.c0 rhs = ok a ∧ canonQ a ∧
      FIo_Native.aspis_core.field.QM31.mul x.c1 rhs = ok b ∧ canonQ b ∧
      FIo_Native.aspis_core.field.wide_exact.WideExact.mul_qm31 x y = ok ⟨a,b⟩ := by
  obtain ⟨rhs,hr,cr,_⟩ := NBG_FieldDischarge.canonical_fio y
  obtain ⟨a,ha,ca,_⟩ := LPi_TowerValues.qm_mul x.c0 rhs hx.1 cr
  obtain ⟨b,hb,cb,_⟩ := LPi_TowerValues.qm_mul x.c1 rhs hx.2 cr
  exact ⟨rhs,a,b,hr,cr,ha,ca,hb,cb,by
    simp only [FIo_Native.aspis_core.field.wide_exact.WideExact.mul_qm31,hr,ha,hb,bind_tc_ok]⟩

theorem scale (x : NE) (s : U32) :
    ∃ rhs a b,
      s % 2147483647#u32 = ok rhs ∧ rhs.val < 2147483647 ∧
      FIo_Native.aspis_core.field.QM31.mul_m31 x.c0 rhs = ok a ∧ canonQ a ∧
      FIo_Native.aspis_core.field.QM31.mul_m31 x.c1 rhs = ok b ∧ canonQ b ∧
      FIo_Native.aspis_core.field.wide_exact.WideExact.mul_m31 x s = ok ⟨a,b⟩ := by
  obtain ⟨rhs,hr,vr⟩ := NBG_WideCarriers.remainder s
  have cr : rhs.val < 2147483647 := by rw [vr]; exact Nat.mod_lt _ (by decide)
  obtain ⟨a,ha,ca,_⟩ := LPi_MixedValues.qm_m31 x.c0 rhs
  obtain ⟨b,hb,cb,_⟩ := LPi_MixedValues.qm_m31 x.c1 rhs
  exact ⟨rhs,a,b,hr,cr,ha,ca,hb,cb,by
    simp only [FIo_Native.aspis_core.field.wide_exact.WideExact.mul_m31,
      FIo_Native.aspis_core.field.P,hr,ha,hb,bind_tc_ok]⟩

#print axioms multiply
#print axioms mixed
#print axioms scale
end NEB_WideCalls
