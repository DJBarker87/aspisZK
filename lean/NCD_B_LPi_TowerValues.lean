-- Inherited body, import-only deployed-cohort retarget.
import NCD_B_LPi_FieldValues
set_option autoImplicit false
namespace AspisR1.LPi_TowerValues
open Aeneas Aeneas.Std Result LPi_FieldValues

theorem qm_add (x y : NQ) (hx : canonQ x) (hy : canonQ y) :
    ∃ z, FIo_Native.aspis_core.field.QM31.add x y = ok z ∧ canonQ z ∧
      qw z = addQ (qw x) (qw y) := by
  obtain ⟨a,ha,ca,va⟩ := cm_add x.c0 y.c0 hx.1 hy.1
  obtain ⟨b,hb,cb,vb⟩ := cm_add x.c1 y.c1 hx.2 hy.2
  refine ⟨⟨a,b⟩,?_,⟨ca,cb⟩,Prod.ext va vb⟩
  simp only [FIo_Native.aspis_core.field.QM31.add,ha,hb,bind_tc_ok]

theorem qm_sub (x y : NQ) (hx : canonQ x) (hy : canonQ y) :
    ∃ z, FIo_Native.aspis_core.field.QM31.sub x y = ok z ∧ canonQ z ∧
      qw z = subQ (qw x) (qw y) := by
  obtain ⟨a,ha,ca,va⟩ := cm_sub x.c0 y.c0 hx.1 hy.1
  obtain ⟨b,hb,cb,vb⟩ := cm_sub x.c1 y.c1 hx.2 hy.2
  refine ⟨⟨a,b⟩,?_,⟨ca,cb⟩,Prod.ext va vb⟩
  simp only [FIo_Native.aspis_core.field.QM31.sub,ha,hb,bind_tc_ok]

theorem qm_mul (x y : NQ) (hx : canonQ x) (hy : canonQ y) :
    ∃ z, FIo_Native.aspis_core.field.QM31.mul x y = ok z ∧ canonQ z ∧
      qw z = mulQ (qw x) (qw y) := by
  obtain ⟨ac,hac,cac,vac⟩ := cm_mul x.c0 y.c0 hx.1 hy.1
  obtain ⟨bd,hbd,cbd,vbd⟩ := cm_mul x.c1 y.c1 hx.2 hy.2
  obtain ⟨a,ha,ca,va⟩ := cm_add x.c0 x.c1 hx.1 hx.2
  obtain ⟨b,hb,cb,vb⟩ := cm_add y.c0 y.c1 hy.1 hy.2
  obtain ⟨cross,hcross,ccross,vcross⟩ := cm_mul a b ca cb
  obtain ⟨r,hr,cr,vr⟩ := by_r bd cbd
  obtain ⟨lo,hlo,clo,vlo⟩ := cm_add ac r cac cr
  obtain ⟨diff,hdiff,cdiff,vdiff⟩ := cm_sub cross ac ccross cac
  obtain ⟨hi,hhi,chi,vhi⟩ := cm_sub diff bd cdiff cbd
  refine ⟨⟨lo,hi⟩,?_,⟨clo,chi⟩,?_⟩
  · simp only [FIo_Native.aspis_core.field.QM31.mul,hac,hbd,ha,hb,hcross,hr,hlo,hdiff,hhi,bind_tc_ok]
  · simp only [qw,mulQ]
    rw [vlo,vhi,vdiff,vr,vcross,va,vb,vac,vbd]


theorem mul_u (x : NQ) (hx : canonQ x) :
    ∃ z, FIo_Native.aspis_core.field.wide_exact.mul_u x = ok z ∧ canonQ z ∧
      qw z = mulU (qw x) := by
  obtain ⟨a,ha,ca,va⟩ := by_r x.c1 hx.2
  refine ⟨⟨a,x.c0⟩,?_,⟨ca,hx.1⟩,Prod.ext va rfl⟩
  simp only [FIo_Native.aspis_core.field.wide_exact.mul_u,ha,bind_tc_ok]

theorem wide_mul (x y : NE) (hx : canonE x) (hy : canonE y) :
    ∃ z, FIo_Native.aspis_core.field.wide_exact.WideExact.mul x y = ok z ∧ canonE z ∧
      ew z = mulE (ew x) (ew y) := by
  obtain ⟨ac,hac,cac,vac⟩ := qm_mul x.c0 y.c0 hx.1 hy.1
  obtain ⟨bd,hbd,cbd,vbd⟩ := qm_mul x.c1 y.c1 hx.2 hy.2
  obtain ⟨a,ha,ca,va⟩ := qm_add x.c0 x.c1 hx.1 hx.2
  obtain ⟨b,hb,cb,vb⟩ := qm_add y.c0 y.c1 hy.1 hy.2
  obtain ⟨cross,hcross,ccross,vcross⟩ := qm_mul a b ca cb
  obtain ⟨r,hr,cr,vr⟩ := mul_u bd cbd
  obtain ⟨lo,hlo,clo,vlo⟩ := qm_add ac r cac cr
  obtain ⟨diff,hdiff,cdiff,vdiff⟩ := qm_sub cross ac ccross cac
  obtain ⟨hi,hhi,chi,vhi⟩ := qm_sub diff bd cdiff cbd
  refine ⟨⟨lo,hi⟩,?_,⟨clo,chi⟩,?_⟩
  · simp only [FIo_Native.aspis_core.field.wide_exact.WideExact.mul,hac,hbd,ha,hb,hcross,hr,hlo,hdiff,hhi,bind_tc_ok]
  · simp only [ew,mulE]
    rw [vlo,vhi,vdiff,vr,vcross,va,vb,vac,vbd]

#print axioms qm_add
#print axioms qm_sub
#print axioms qm_mul
#print axioms mul_u
#print axioms wide_mul
end AspisR1.LPi_TowerValues
