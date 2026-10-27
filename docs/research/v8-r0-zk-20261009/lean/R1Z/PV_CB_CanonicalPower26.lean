import R1Z.PV_CB_CanonicalQuarticMore
import R1Z.PV_CB_MaskSource
set_option autoImplicit false
namespace R1Z.PV_CB_CanonicalPower26
open Aeneas Aeneas.Std Result PV_CB_CanonicalTower

theorem power26 (input : Q) (valid : Valid input) :
    ∃ value, PV_CB_MaskSource.state_only_hiding.mask_power_26 input = ok value ∧ Valid value := by
  obtain ⟨x2,h2,v2⟩ := PV_CB_CanonicalQuarticMore.square input valid
  obtain ⟨x4,h4,v4⟩ := PV_CB_CanonicalQuarticMore.square x2 v2
  obtain ⟨x8,h8,v8⟩ := PV_CB_CanonicalQuarticMore.square x4 v4
  obtain ⟨x16,h16,v16⟩ := PV_CB_CanonicalQuarticMore.square x8 v8
  obtain ⟨x24,h24,v24⟩ := PV_CB_CanonicalQuartic.mul x16 x8 v16 v8
  obtain ⟨out,hout,vout⟩ := PV_CB_CanonicalQuartic.mul x24 x2 v24 v2
  refine ⟨out,?_,vout⟩
  simp only [PV_CB_MaskSource.state_only_hiding.mask_power_26,
    PV_CB_CurrentQuartic.S.square,PV_CB_CurrentQuartic.S.mul] at h2 h4 h8 h16 h24 hout ⊢
  simp only [h2,h4,h8,h16,h24,hout,bind_tc_ok]
#print axioms power26
end R1Z.PV_CB_CanonicalPower26
