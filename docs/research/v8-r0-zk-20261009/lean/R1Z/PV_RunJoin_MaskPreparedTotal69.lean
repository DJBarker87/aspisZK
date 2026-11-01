import R1Z.PV_RunJoin_MaskFieldTotal69
import R1Z.ProverRwP6ArrayRead
set_option autoImplicit false
namespace R1Z.PV_RunJoin_MaskPreparedTotal69
open Aeneas Aeneas.Std Result PV_B3_Copy_117 PV_RunJoin_MaskFieldTotal69

theorem component (left : Array U32 3#usize) (right : C) : ∃ out,host_arithmetic.prepared_component_mul left right=ok out := by
  obtain ⟨m,h_m⟩ := ProverRwP6ArrayRead.read left 0#usize (by decide)
  obtain ⟨m0,h_m0⟩ := PV_RunJoin_MaskScalarTotal69.mul m right.a
  obtain ⟨m1,h_m1⟩ := ProverRwP6ArrayRead.read left 1#usize (by decide)
  obtain ⟨m11,h_m11⟩ := PV_RunJoin_MaskScalarTotal69.mul m1 right.b
  obtain ⟨m2,h_m2⟩ := ProverRwP6ArrayRead.read left 2#usize (by decide)
  obtain ⟨m3,h_m3⟩ := PV_RunJoin_MaskScalarTotal69.add right.a right.b
  obtain ⟨m21,h_m21⟩ := PV_RunJoin_MaskScalarTotal69.mul m2 m3
  obtain ⟨m4,h_m4⟩ := PV_RunJoin_MaskScalarTotal69.sub m0 m11
  obtain ⟨m5,h_m5⟩ := PV_RunJoin_MaskScalarTotal69.sub m21 m0
  obtain ⟨m6,h_m6⟩ := PV_RunJoin_MaskScalarTotal69.sub m5 m11
  simp only [host_arithmetic.prepared_component_mul,bind_tc_ok,h_m,h_m0,h_m1,h_m11,h_m2,h_m3,h_m21,h_m4,h_m5,h_m6]
  exact ⟨_,rfl⟩

theorem mul (self : host_arithmetic.PreparedQm31Multiplier) (rhs : Q) : ∃ out,host_arithmetic.PreparedQm31Multiplier.mul self rhs=ok out := by
  obtain ⟨a,h_a⟩ := ProverRwP6ArrayRead.read self.components 0#usize (by decide)
  obtain ⟨m0,h_m0⟩ := component a rhs.c0
  obtain ⟨a1,h_a1⟩ := ProverRwP6ArrayRead.read self.components 1#usize (by decide)
  obtain ⟨m1,h_m1⟩ := component a1 rhs.c1
  obtain ⟨a2,h_a2⟩ := ProverRwP6ArrayRead.read self.components 2#usize (by decide)
  obtain ⟨c,h_c⟩ := cadd rhs.c0 rhs.c1
  obtain ⟨m2,h_m2⟩ := component a2 c
  obtain ⟨c1,h_c1⟩ := hostR m1
  obtain ⟨c2,h_c2⟩ := cadd m0 c1
  obtain ⟨c3,h_c3⟩ := csub m2 m0
  obtain ⟨c4,h_c4⟩ := csub c3 m1
  simp only [host_arithmetic.PreparedQm31Multiplier.mul,bind_tc_ok,h_a,h_m0,h_a1,h_m1,h_a2,h_c,h_m2,h_c1,h_c2,h_c3,h_c4]
  exact ⟨_,rfl⟩

theorem prepareComponent (component : C) : ∃ out,host_arithmetic.prepare_component component=ok out := by
  obtain ⟨m,h_m⟩ := PV_RunJoin_MaskScalarTotal69.add component.a component.b
  simp only [host_arithmetic.prepare_component,bind_tc_ok,h_m]
  exact ⟨_,rfl⟩

theorem prepare (value : Q) : ∃ out,host_arithmetic.PreparedQm31Multiplier.new value=ok out := by
  obtain ⟨a,h_a⟩ := prepareComponent value.c0
  obtain ⟨a1,h_a1⟩ := prepareComponent value.c1
  obtain ⟨c,h_c⟩ := cadd value.c0 value.c1
  obtain ⟨a2,h_a2⟩ := prepareComponent c
  simp only [host_arithmetic.PreparedQm31Multiplier.new,bind_tc_ok,h_a,h_a1,h_c,h_a2]
  exact ⟨_,rfl⟩

theorem power (value : Q) : ∃ out,host_arithmetic.mask_power_26 value=ok out := by
  obtain ⟨x2,h_x2⟩ := qsquare value
  obtain ⟨x4,h_x4⟩ := qsquare x2
  obtain ⟨x8,h_x8⟩ := qsquare x4
  obtain ⟨x16,h_x16⟩ := qsquare x8
  obtain ⟨q,h_q⟩ := qmul x16 x8
  obtain ⟨out,h_out⟩ := qmul q x2
  simp only [host_arithmetic.mask_power_26,bind_tc_ok,h_x2,h_x4,h_x8,h_x16,h_q,h_out]
  exact ⟨_,rfl⟩

theorem tower (a : Q) (i : Usize) (bound : i.val<4) :
    ∃ out,host_arithmetic.mul_tower_basis a i=ok out := by
  unfold host_arithmetic.mul_tower_basis
  have cases : i.val=0 ∨ i.val=1 ∨ i.val=2 ∨ i.val=3 := by omega
  rcases cases with h|h|h|h <;> rw [h]
  all_goals
    repeat' first
      | (apply ProverRwP6BindTotal.bind_total _ _ (hostR _); intro _)
      | (apply ProverRwP6BindTotal.bind_total _ _ (hostI _); intro _)
    exact ⟨_,rfl⟩


#print axioms component
#print axioms mul
#print axioms prepareComponent
#print axioms prepare
#print axioms power
#print axioms tower
end R1Z.PV_RunJoin_MaskPreparedTotal69
