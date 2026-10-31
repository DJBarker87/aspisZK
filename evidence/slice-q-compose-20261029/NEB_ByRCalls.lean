import NEB_FieldDomains
set_option autoImplicit false
namespace NEB_ByRCalls
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues

theorem source (x : NC) (hx : canonC x) :
    ∃ da re db im : U32,
      FIo_Native.aspis_core.field.M31.double x.a = ok da ∧ da.val < 2147483647 ∧
      FIo_Native.aspis_core.field.M31.sub da x.b = ok re ∧ re.val < 2147483647 ∧
      FIo_Native.aspis_core.field.M31.double x.b = ok db ∧ db.val < 2147483647 ∧
      FIo_Native.aspis_core.field.M31.add x.a db = ok im ∧ im.val < 2147483647 ∧
      FIo_Native.aspis_core.field.mul_by_r x = ok ⟨re,im⟩ := by
  obtain ⟨da,ha,_,ca⟩ := LPi_NatBase.add x.a x.a hx.1 hx.1
  obtain ⟨re,hr,_,cr⟩ := LPi_NatBase.sub da x.b ca hx.2
  obtain ⟨db,hb,_,cb⟩ := LPi_NatBase.add x.b x.b hx.2 hx.2
  obtain ⟨im,hi,_,ci⟩ := LPi_NatBase.add x.a db hx.1 cb
  exact ⟨da,re,db,im,ha,ca,hr,cr,hb,cb,hi,ci,by
    simp only [FIo_Native.aspis_core.field.mul_by_r,FIo_Native.aspis_core.field.M31.double,
      ha,hr,hb,hi,bind_tc_ok]⟩

theorem mul_u (x : NQ) (hx : canonQ x) :
    canonC x.c1 ∧ ∃ r,
      FIo_Native.aspis_core.field.mul_by_r x.c1 = ok r ∧ canonC r ∧
      FIo_Native.aspis_core.field.wide_exact.mul_u x = ok ⟨r,x.c0⟩ ∧
      canonQ (⟨r,x.c0⟩ : NQ) := by
  obtain ⟨r,hr,cr,_⟩ := by_r x.c1 hx.2
  exact ⟨hx.2,r,hr,cr,by
    simp only [FIo_Native.aspis_core.field.wide_exact.mul_u,hr,bind_tc_ok],cr,hx.1⟩
#print axioms source
#print axioms mul_u
end NEB_ByRCalls
