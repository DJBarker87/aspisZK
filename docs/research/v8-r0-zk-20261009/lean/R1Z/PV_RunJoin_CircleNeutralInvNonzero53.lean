import R1Z.PV_RunJoin_CircleNeutralSquareN53
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleNeutralInvNonzero53
open PV_RunJoin_CircleNeutralShape53

theorem nonzero (self : U32) (hcself : Canon self) (hne : (self != 0#u32)=true) :
    ∃ y, PV_RunJoin_CircleRawScalar52.field.M31.inv self = ok y ∧
      PV_RunJoin_CircleR72Raw52.field.M31.inv self = ok y ∧ Canon y := by
  obtain ⟨m,h0,h0',hcm⟩ := PV_RunJoin_CircleNeutralMul53.complete self self hcself hcself
  obtain ⟨t2,h1,h1',hct2⟩ := PV_RunJoin_CircleNeutralMul53.complete m self hcm hcself
  obtain ⟨m1,h2,h2',hcm1⟩ := PV_RunJoin_CircleNeutralSquareN53.complete t2 hct2 2#usize
  obtain ⟨t4,h3,h3',hct4⟩ := PV_RunJoin_CircleNeutralMul53.complete m1 t2 hcm1 hct2
  obtain ⟨m2,h4,h4',hcm2⟩ := PV_RunJoin_CircleNeutralSquareN53.complete t4 hct4 4#usize
  obtain ⟨t8,h5,h5',hct8⟩ := PV_RunJoin_CircleNeutralMul53.complete m2 t4 hcm2 hct4
  obtain ⟨m3,h6,h6',hcm3⟩ := PV_RunJoin_CircleNeutralSquareN53.complete t8 hct8 8#usize
  obtain ⟨t16,h7,h7',hct16⟩ := PV_RunJoin_CircleNeutralMul53.complete m3 t8 hcm3 hct8
  obtain ⟨m4,h8,h8',hcm4⟩ := PV_RunJoin_CircleNeutralSquareN53.complete t16 hct16 8#usize
  obtain ⟨t24,h9,h9',hct24⟩ := PV_RunJoin_CircleNeutralMul53.complete m4 t8 hcm4 hct8
  obtain ⟨m5,h10,h10',hcm5⟩ := PV_RunJoin_CircleNeutralSquareN53.complete t24 hct24 4#usize
  obtain ⟨t28,h11,h11',hct28⟩ := PV_RunJoin_CircleNeutralMul53.complete m5 t4 hcm5 hct4
  obtain ⟨m6,h12,h12',hcm6⟩ := PV_RunJoin_CircleNeutralMul53.complete t28 t28 hct28 hct28
  obtain ⟨t29,h13,h13',hct29⟩ := PV_RunJoin_CircleNeutralMul53.complete m6 self hcm6 hcself
  obtain ⟨t30,h14,h14',hct30⟩ := PV_RunJoin_CircleNeutralMul53.complete t29 t29 hct29 hct29
  obtain ⟨m7,h15,h15',hcm7⟩ := PV_RunJoin_CircleNeutralMul53.complete t30 t30 hct30 hct30
  obtain ⟨out,h16,h16',hcout⟩ := PV_RunJoin_CircleNeutralMul53.complete m7 self hcm7 hcself
  refine ⟨out,?_,?_,hcout⟩
  · unfold PV_RunJoin_CircleRawScalar52.field.M31.inv
    simp only [massert,hne,if_true,bind_tc_ok,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16]
  · unfold PV_RunJoin_CircleR72Raw52.field.M31.inv
    simp only [massert,hne,if_true,bind_tc_ok,h0',h1',h2',h3',h4',h5',h6',h7',h8',h9',h10',h11',h12',h13',h14',h15',h16']

#print axioms nonzero
end R1Z.PV_RunJoin_CircleNeutralInvNonzero53
