import NEB_SquareDomains
import NBG_InverseBridge
set_option autoImplicit false
noncomputable section
namespace NEB_InverseCalls
open Aeneas Aeneas.Std Result AspisR1

/-- The actual seventeen-call DAG; no canonical input assumption or inner
callee domain/interpretation hypothesis is added. Zero is handled separately. -/
theorem nonzero (x : U32) (nonzero : x != 0#u32) :
    ∃ m t2 m1 t4 m2 t8 m3 t16 m4 t24 m5 t28 m6 t29 t30 m7 out : U32,
      FIo_Native.aspis_core.field.M31.mul x x=ok m ∧ m.val<2147483647 ∧
      FIo_Native.aspis_core.field.M31.mul m x=ok t2 ∧ t2.val<2147483647 ∧
      AspisR1M31Inverse.field.square_n FIo_Native.aspis_core.field.M31.mul t2 2#usize=ok m1 ∧ m1.val<2147483647 ∧
      FIo_Native.aspis_core.field.M31.mul m1 t2=ok t4 ∧ t4.val<2147483647 ∧
      AspisR1M31Inverse.field.square_n FIo_Native.aspis_core.field.M31.mul t4 4#usize=ok m2 ∧ m2.val<2147483647 ∧
      FIo_Native.aspis_core.field.M31.mul m2 t4=ok t8 ∧ t8.val<2147483647 ∧
      AspisR1M31Inverse.field.square_n FIo_Native.aspis_core.field.M31.mul t8 8#usize=ok m3 ∧ m3.val<2147483647 ∧
      FIo_Native.aspis_core.field.M31.mul m3 t8=ok t16 ∧ t16.val<2147483647 ∧
      AspisR1M31Inverse.field.square_n FIo_Native.aspis_core.field.M31.mul t16 8#usize=ok m4 ∧ m4.val<2147483647 ∧
      FIo_Native.aspis_core.field.M31.mul m4 t8=ok t24 ∧ t24.val<2147483647 ∧
      AspisR1M31Inverse.field.square_n FIo_Native.aspis_core.field.M31.mul t24 4#usize=ok m5 ∧ m5.val<2147483647 ∧
      FIo_Native.aspis_core.field.M31.mul m5 t4=ok t28 ∧ t28.val<2147483647 ∧
      FIo_Native.aspis_core.field.M31.mul t28 t28=ok m6 ∧ m6.val<2147483647 ∧
      FIo_Native.aspis_core.field.M31.mul m6 x=ok t29 ∧ t29.val<2147483647 ∧
      FIo_Native.aspis_core.field.M31.mul t29 t29=ok t30 ∧ t30.val<2147483647 ∧
      FIo_Native.aspis_core.field.M31.mul t30 t30=ok m7 ∧ m7.val<2147483647 ∧
      FIo_Native.aspis_core.field.M31.mul m7 x=ok out ∧ out.val<2147483647 ∧
      AspisR1M31Inverse.field.M31.inv FIo_Native.aspis_core.field.M31.mul x=ok out := by
  obtain ⟨m,h_m,_,c_m⟩ := LPf_BaseMultiply.source x x
  obtain ⟨t2,h_t2,_,c_t2⟩ := LPf_BaseMultiply.source m x
  obtain ⟨m1,h_m1,_,c_m10⟩ := NEB_SquareDomains.source t2 2#usize
  have c_m1 : m1.val<2147483647 := c_m10 (by decide)
  obtain ⟨t4,h_t4,_,c_t4⟩ := LPf_BaseMultiply.source m1 t2
  obtain ⟨m2,h_m2,_,c_m20⟩ := NEB_SquareDomains.source t4 4#usize
  have c_m2 : m2.val<2147483647 := c_m20 (by decide)
  obtain ⟨t8,h_t8,_,c_t8⟩ := LPf_BaseMultiply.source m2 t4
  obtain ⟨m3,h_m3,_,c_m30⟩ := NEB_SquareDomains.source t8 8#usize
  have c_m3 : m3.val<2147483647 := c_m30 (by decide)
  obtain ⟨t16,h_t16,_,c_t16⟩ := LPf_BaseMultiply.source m3 t8
  obtain ⟨m4,h_m4,_,c_m40⟩ := NEB_SquareDomains.source t16 8#usize
  have c_m4 : m4.val<2147483647 := c_m40 (by decide)
  obtain ⟨t24,h_t24,_,c_t24⟩ := LPf_BaseMultiply.source m4 t8
  obtain ⟨m5,h_m5,_,c_m50⟩ := NEB_SquareDomains.source t24 4#usize
  have c_m5 : m5.val<2147483647 := c_m50 (by decide)
  obtain ⟨t28,h_t28,_,c_t28⟩ := LPf_BaseMultiply.source m5 t4
  obtain ⟨m6,h_m6,_,c_m6⟩ := LPf_BaseMultiply.source t28 t28
  obtain ⟨t29,h_t29,_,c_t29⟩ := LPf_BaseMultiply.source m6 x
  obtain ⟨t30,h_t30,_,c_t30⟩ := LPf_BaseMultiply.source t29 t29
  obtain ⟨m7,h_m7,_,c_m7⟩ := LPf_BaseMultiply.source t30 t30
  obtain ⟨out,h_out,_,c_out⟩ := LPf_BaseMultiply.source m7 x
  refine ⟨m,t2,m1,t4,m2,t8,m3,t16,m4,t24,m5,t28,m6,t29,t30,m7,out,h_m,c_m,h_t2,c_t2,h_m1,c_m1,h_t4,c_t4,h_m2,c_m2,h_t8,c_t8,h_m3,c_m3,h_t16,c_t16,h_m4,c_m4,h_t24,c_t24,h_m5,c_m5,h_t28,c_t28,h_m6,c_m6,h_t29,c_t29,h_t30,c_t30,h_m7,c_m7,h_out,c_out,?_⟩
  simp only [AspisR1M31Inverse.field.M31.inv,nonzero,massert_true,bind_tc_ok,
    h_m,h_t2,h_m1,h_t4,h_m2,h_t8,h_m3,h_t16,h_m4,h_t24,h_m5,h_t28,h_m6,h_t29,h_t30,h_m7,h_out]

theorem zero : AspisR1M31Inverse.field.M31.inv FIo_Native.aspis_core.field.M31.mul 0#u32 =
    Port4C_InverseExecution.inverse_owned 0#u32 := NBG_InverseBridge.inverse_result _

#print axioms nonzero
#print axioms zero
end NEB_InverseCalls
end
