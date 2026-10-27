import R1Z.PV_CB_CanonicalNeg
import R1Z.PV_CB_CanonicalComplex
import R1Z.PV_CB_MaskLeaves
set_option autoImplicit false
namespace R1Z.PV_CB_CanonicalMaskBasis
open Aeneas Aeneas.Std Result
abbrev C := PV_CB_CanonicalComplex.C
abbrev Q := PV_CB_CanonicalTower.Q

theorem r (value : C) (valid : PV_CB_CanonicalComplex.Valid value) :
    ∃ out, PV_CB_MaskLeaves.S.r value = ok out ∧ PV_CB_CanonicalComplex.Valid out := by
  have same : PV_CB_MaskLeaves.S.r value = PV_CB_CurrentQuartic.S.r value := rfl
  obtain ⟨out,hout,vout⟩ := PV_CB_CanonicalComplex.r value valid
  exact ⟨out,same.trans hout,vout⟩

theorem i (value : C) (valid : PV_CB_CanonicalComplex.Valid value) :
    ∃ out, PV_CB_MaskLeaves.S.i value = ok out ∧ PV_CB_CanonicalComplex.Valid out := by
  obtain ⟨negative,hnegative,vnegative⟩ := PV_CB_CanonicalNeg.neg value.b valid.2
  refine ⟨⟨negative,value.a⟩,?_,⟨vnegative,valid.1⟩⟩
  simp only [PV_CB_MaskLeaves.S.i,PV_CB_MaskSource.state_only_hiding.cm31_mul_i,
    PV_CB_CurrentNeg.source] at hnegative ⊢
  simp only [hnegative,bind_tc_ok,ProverRwP7CurrentFieldSource.aspis_core.field.CM31.new]

theorem tower (value : Q) (coordinate : Usize) (bound : coordinate.val < 4)
    (valid : PV_CB_CanonicalTower.Valid value) :
    ∃ out, PV_CB_MaskLeaves.S.tower value coordinate = ok out ∧ PV_CB_CanonicalTower.Valid out := by
  have cases : coordinate.val=0 ∨ coordinate.val=1 ∨ coordinate.val=2 ∨ coordinate.val=3 := by omega
  rcases cases with h | h | h | h
  · exact ⟨value,by simp only [PV_CB_MaskLeaves.S.tower,
      PV_CB_MaskSource.state_only_hiding.mul_tower_basis,h],valid⟩
  · obtain ⟨a,ha,va⟩ := i value.c0 valid.1
    obtain ⟨b,hb,vb⟩ := i value.c1 valid.2
    refine ⟨⟨a,b⟩,?_,⟨va,vb⟩⟩
    simp only [PV_CB_MaskLeaves.S.tower,PV_CB_MaskSource.state_only_hiding.mul_tower_basis,
      h,ha,hb,bind_tc_ok]
  · obtain ⟨a,ha,va⟩ := r value.c1 valid.2
    refine ⟨⟨a,value.c0⟩,?_,⟨va,valid.1⟩⟩
    simp only [PV_CB_MaskLeaves.S.tower,PV_CB_MaskSource.state_only_hiding.mul_tower_basis,
      h,ha,bind_tc_ok]
  · obtain ⟨a,ha,va⟩ := r value.c1 valid.2
    obtain ⟨b,hb,vb⟩ := i a va
    obtain ⟨c,hc,vc⟩ := i value.c0 valid.1
    refine ⟨⟨b,c⟩,?_,⟨vb,vc⟩⟩
    simp only [PV_CB_MaskLeaves.S.tower,PV_CB_MaskSource.state_only_hiding.mul_tower_basis,
      h,ha,hb,hc,bind_tc_ok]
#print axioms r
#print axioms i
#print axioms tower
end R1Z.PV_CB_CanonicalMaskBasis
