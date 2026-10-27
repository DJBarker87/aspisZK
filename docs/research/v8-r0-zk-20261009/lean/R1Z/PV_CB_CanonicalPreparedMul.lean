import R1Z.PV_CB_CanonicalPreparedPart
set_option autoImplicit false
namespace R1Z.PV_CB_CanonicalPreparedMul
open Aeneas Aeneas.Std Result PV_CB_CanonicalPreparedCtor

theorem mul (prepared : Prepared) (right : Q) (hp : Valid prepared)
    (hr : PV_CB_CanonicalTower.Valid right) :
    ∃ out, PV_CB_PreparedTotal.S.mul prepared right = ok out ∧
      PV_CB_CanonicalTower.Valid out := by
  obtain ⟨a,ha,va⟩ := PV_CB_CanonicalArrays.read PartValid prepared.components hp 0#usize (by decide)
  obtain ⟨b,hb,vb⟩ := PV_CB_CanonicalArrays.read PartValid prepared.components hp 1#usize (by decide)
  obtain ⟨c,hc,vc⟩ := PV_CB_CanonicalArrays.read PartValid prepared.components hp 2#usize (by decide)
  obtain ⟨m0,h0,v0⟩ := PV_CB_CanonicalPreparedPart.mul_part a right.c0 va hr.1
  obtain ⟨m1,h1,v1⟩ := PV_CB_CanonicalPreparedPart.mul_part b right.c1 vb hr.2
  obtain ⟨sum,hsum,vsum⟩ := PV_CB_CanonicalComplex.add right.c0 right.c1 hr.1 hr.2
  obtain ⟨m2,h2,v2⟩ := PV_CB_CanonicalPreparedPart.mul_part c sum vc vsum
  obtain ⟨r,hr1,vr⟩ := PV_CB_CanonicalComplex.r m1 v1
  obtain ⟨real,hreal,vreal⟩ := PV_CB_CanonicalComplex.add m0 r v0 vr
  obtain ⟨cross,hcross,vcross⟩ := PV_CB_CanonicalComplex.sub m2 m0 v2 v0
  obtain ⟨imaginary,himaginary,vimaginary⟩ := PV_CB_CanonicalComplex.sub cross m1 vcross v1
  refine ⟨⟨real,imaginary⟩,?_,⟨vreal,vimaginary⟩⟩
  simp only [PV_CB_PreparedTotal.S.mul,
    ProverRwP7CurrentFieldSource.aspis_core.field.PreparedQm31Multiplier.mul,
    PV_CB_CurrentComplex.S.add,PV_CB_CurrentComplex.S.sub,PV_CB_CurrentQuartic.S.r] at hsum hr1 hreal hcross himaginary ⊢
  simp only [ha,hb,hc,h0,h1,hsum,h2,hr1,hreal,hcross,himaginary,bind_tc_ok]
#print axioms mul
end R1Z.PV_CB_CanonicalPreparedMul
