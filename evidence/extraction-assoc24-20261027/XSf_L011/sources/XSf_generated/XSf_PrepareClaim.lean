import XSf_View
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers
set_option autoImplicit false
noncomputable section
namespace XSf_PrepareClaim

theorem change_claim {H : Type} (D : C.D H) (sem : C.Sem H) (v : C.View) (hash : H)
 (old : Array C.E 29#usize) (hi : XRy_WideMultiply.Canonical v.inactive) :
 AspisR1PublicPreparation.PreparedScratchModel.prepare XRy_PreparePowers.exceptClaim D sem v hash old =
 AspisR1PublicPreparation.PreparedScratchModel.prepare XRo_Join_Installed.actual D sem v hash old := by
 unfold AspisR1PublicPreparation.PreparedScratchModel.prepare
 simp only [XRy_PreparePowers.exceptClaim,XRo_Join_Installed.powers_slot]
 apply (bind_eq_iff _ _ _).mpr
 intro state hs
 apply (bind_eq_iff _ _ _).mpr
 intro t ht
 apply (bind_eq_iff _ _ _).mpr
 rintro ⟨gamma,t1⟩ hg
 have hc := XRy_PreparePowers.gamma_canonical D t t1 27#u8 v.y1 gamma hg
 obtain ⟨g,_,hp,hgc⟩ := XSa_PowersDimensions.twenty_nine gamma hc
 apply (bind_eq_iff _ _ _).mpr
 intro bytes hb
 apply (bind_eq_iff _ _ _).mpr
 intro payload hpayload
 apply (bind_eq_iff _ _ _).mpr
 rintro ⟨kappa,t2⟩ hk
 have hkc := XSf_Reached.kappa D t1 t2 28#u8 payload kappa hk
 have hclaim := XSa_CachedClaim.claim D sem v.y1 v.inactive kappa g hi hkc hgc
 simp only [hp,bind_tc_ok]
 simp only [hclaim]

#print axioms change_claim
end XSf_PrepareClaim
end
