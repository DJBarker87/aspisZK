import LPq_FieldPorts
set_option autoImplicit false
namespace AspisR1.LPq_TowerPorts
open Aeneas Aeneas.Std Result LPi_FieldValues LPq_FieldPorts XRo_Join_Carriers

theorem add (x y : NQ) (hx : canonQ x) (hy : canonQ y) :
    ∃ z, FIo_Native.aspis_core.field.QM31.add x y=ok z ∧ canonQ z ∧
      XRn_Join_Field.field.QM31.add (qm x) (qm y)=ok (qm z) := by
  obtain ⟨a,ha,ca,ea⟩ := LPq_FieldPorts.cm_add x.c0 y.c0 hx.1 hy.1
  obtain ⟨b,hb,cb,eb⟩ := LPq_FieldPorts.cm_add x.c1 y.c1 hx.2 hy.2
  exact ⟨⟨a,b⟩,by simp only [FIo_Native.aspis_core.field.QM31.add,ha,hb,bind_tc_ok],
    ⟨ca,cb⟩,by simp only [XRn_Join_Field.field.QM31.add,qm,ea,eb,bind_tc_ok]⟩

theorem sub (x y : NQ) (hx : canonQ x) (hy : canonQ y) :
    ∃ z, FIo_Native.aspis_core.field.QM31.sub x y=ok z ∧ canonQ z ∧
      XRn_Join_Field.field.QM31.sub (qm x) (qm y)=ok (qm z) := by
  obtain ⟨a,ha,ca,ea⟩ := LPq_FieldPorts.cm_sub x.c0 y.c0 hx.1 hy.1
  obtain ⟨b,hb,cb,eb⟩ := LPq_FieldPorts.cm_sub x.c1 y.c1 hx.2 hy.2
  exact ⟨⟨a,b⟩,by simp only [FIo_Native.aspis_core.field.QM31.sub,ha,hb,bind_tc_ok],
    ⟨ca,cb⟩,by simp only [XRn_Join_Field.field.QM31.sub,qm,ea,eb,bind_tc_ok]⟩

theorem mul (x y : NQ) (hx : canonQ x) (hy : canonQ y) :
    ∃ z, FIo_Native.aspis_core.field.QM31.mul x y=ok z ∧ canonQ z ∧
      XRn_Join_Field.field.QM31.mul (qm x) (qm y)=ok (qm z) := by
  obtain ⟨ac,hac,cac,eac⟩ := LPq_FieldPorts.cm_mul x.c0 y.c0 hx.1 hy.1
  obtain ⟨bd,hbd,cbd,ebd⟩ := LPq_FieldPorts.cm_mul x.c1 y.c1 hx.2 hy.2
  obtain ⟨a,ha,ca,ea⟩ := LPq_FieldPorts.cm_add x.c0 x.c1 hx.1 hx.2
  obtain ⟨b,hb,cb,eb⟩ := LPq_FieldPorts.cm_add y.c0 y.c1 hy.1 hy.2
  obtain ⟨cross,hcross,ccross,ecross⟩ := LPq_FieldPorts.cm_mul a b ca cb
  obtain ⟨r,hr,cr,er⟩ := LPq_FieldPorts.by_r bd cbd
  obtain ⟨lo,hlo,clo,elo⟩ := LPq_FieldPorts.cm_add ac r cac cr
  obtain ⟨d,hd,cd,ed⟩ := LPq_FieldPorts.cm_sub cross ac ccross cac
  obtain ⟨hi,hhi,chi,ehi⟩ := LPq_FieldPorts.cm_sub d bd cd cbd
  exact ⟨⟨lo,hi⟩,by simp only [FIo_Native.aspis_core.field.QM31.mul,
    hac,hbd,ha,hb,hcross,hr,hlo,hd,hhi,bind_tc_ok],⟨clo,chi⟩,
    by simp only [XRn_Join_Field.field.QM31.mul,qm,eac,ebd,ea,eb,ecross,er,elo,ed,ehi,bind_tc_ok]⟩

theorem mul_u (x : NQ) (hx : canonQ x) :
    ∃ z, FIo_Native.aspis_core.field.wide_exact.mul_u x=ok z ∧ canonQ z ∧
      XRn_Join_Field.field.wide_exact.mul_u (qm x)=ok (qm z) := by
  obtain ⟨a,ha,ca,ea⟩ := LPq_FieldPorts.by_r x.c1 hx.2
  exact ⟨⟨a,x.c0⟩,by simp only [FIo_Native.aspis_core.field.wide_exact.mul_u,ha,bind_tc_ok],
    ⟨ca,hx.1⟩,by simp only [XRn_Join_Field.field.wide_exact.mul_u,qm,ea,bind_tc_ok]⟩

#print axioms add
#print axioms sub
#print axioms mul
#print axioms mul_u
end AspisR1.LPq_TowerPorts
