import NEB_FieldDomains
set_option autoImplicit false
namespace NEB_QMCalls
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues

/-- The selected witnesses are precisely the emitted body's sequential
returns. Every later domain follows from earlier returns, not an inner premise. -/
theorem multiply (x y : NQ) (hx : canonQ x) (hy : canonQ y) :
    ∃ ac bd a b cross r lo diff hi : NC,
      FIo_Native.aspis_core.field.CM31.mul x.c0 y.c0 = ok ac ∧ canonC ac ∧
      FIo_Native.aspis_core.field.CM31.mul x.c1 y.c1 = ok bd ∧ canonC bd ∧
      FIo_Native.aspis_core.field.CM31.add x.c0 x.c1 = ok a ∧ canonC a ∧
      FIo_Native.aspis_core.field.CM31.add y.c0 y.c1 = ok b ∧ canonC b ∧
      FIo_Native.aspis_core.field.CM31.mul a b = ok cross ∧ canonC cross ∧
      FIo_Native.aspis_core.field.mul_by_r bd = ok r ∧ canonC r ∧
      FIo_Native.aspis_core.field.CM31.add ac r = ok lo ∧ canonC lo ∧
      FIo_Native.aspis_core.field.CM31.sub cross ac = ok diff ∧ canonC diff ∧
      FIo_Native.aspis_core.field.CM31.sub diff bd = ok hi ∧ canonC hi ∧
      FIo_Native.aspis_core.field.QM31.mul x y = ok ⟨lo,hi⟩ := by
  obtain ⟨ac,hac,cac,_⟩ := cm_mul x.c0 y.c0 hx.1 hy.1
  obtain ⟨bd,hbd,cbd,_⟩ := cm_mul x.c1 y.c1 hx.2 hy.2
  obtain ⟨a,ha,ca,_⟩ := cm_add x.c0 x.c1 hx.1 hx.2
  obtain ⟨b,hb,cb,_⟩ := cm_add y.c0 y.c1 hy.1 hy.2
  obtain ⟨cross,hcross,ccross,_⟩ := cm_mul a b ca cb
  obtain ⟨r,hr,cr,_⟩ := by_r bd cbd
  obtain ⟨lo,hlo,clo,_⟩ := cm_add ac r cac cr
  obtain ⟨diff,hdiff,cdiff,_⟩ := cm_sub cross ac ccross cac
  obtain ⟨hi,hhi,chi,_⟩ := cm_sub diff bd cdiff cbd
  exact ⟨ac,bd,a,b,cross,r,lo,diff,hi,hac,cac,hbd,cbd,ha,ca,hb,cb,
    hcross,ccross,hr,cr,hlo,clo,hdiff,cdiff,hhi,chi,by
      simp only [FIo_Native.aspis_core.field.QM31.mul,hac,hbd,ha,hb,hcross,hr,hlo,hdiff,hhi,bind_tc_ok]⟩

theorem add (x y : NQ) (hx : canonQ x) (hy : canonQ y) :
    ∃ a b : NC,
      FIo_Native.aspis_core.field.CM31.add x.c0 y.c0 = ok a ∧ canonC a ∧
      FIo_Native.aspis_core.field.CM31.add x.c1 y.c1 = ok b ∧ canonC b ∧
      FIo_Native.aspis_core.field.QM31.add x y = ok ⟨a,b⟩ := by
  obtain ⟨a,ha,ca,_⟩ := cm_add x.c0 y.c0 hx.1 hy.1
  obtain ⟨b,hb,cb,_⟩ := cm_add x.c1 y.c1 hx.2 hy.2
  exact ⟨a,b,ha,ca,hb,cb,by simp only [FIo_Native.aspis_core.field.QM31.add,ha,hb,bind_tc_ok]⟩

theorem sub (x y : NQ) (hx : canonQ x) (hy : canonQ y) :
    ∃ a b : NC,
      FIo_Native.aspis_core.field.CM31.sub x.c0 y.c0 = ok a ∧ canonC a ∧
      FIo_Native.aspis_core.field.CM31.sub x.c1 y.c1 = ok b ∧ canonC b ∧
      FIo_Native.aspis_core.field.QM31.sub x y = ok ⟨a,b⟩ := by
  obtain ⟨a,ha,ca,_⟩ := cm_sub x.c0 y.c0 hx.1 hy.1
  obtain ⟨b,hb,cb,_⟩ := cm_sub x.c1 y.c1 hx.2 hy.2
  exact ⟨a,b,ha,ca,hb,cb,by simp only [FIo_Native.aspis_core.field.QM31.sub,ha,hb,bind_tc_ok]⟩

#print axioms multiply
#print axioms add
#print axioms sub
end NEB_QMCalls
