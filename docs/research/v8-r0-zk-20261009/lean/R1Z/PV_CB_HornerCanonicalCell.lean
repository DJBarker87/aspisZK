import R1Z.PV_CB_HornerReach
import R1Z.PV_CB_CanonicalHorner
set_option autoImplicit false
namespace R1Z.PV_CB_HornerCanonicalCell
open Aeneas Aeneas.Std Result PV_CB_HornerCell

theorem representative (coeff : Coeff) (p : Prepared) (i : Usize) (shared : Q)
    (inside : i.val < 27) (vc : PV_CB_CanonicalArrays.Valid PV_CB_CanonicalTower.Valid coeff) :
    ∃ value, PV_CB_CanonicalTower.Valid value ∧ cell coeff p i shared = scalar p shared value := by
  obtain ⟨value,hv,vv⟩ := PV_CB_CanonicalArrays.read PV_CB_CanonicalTower.Valid coeff vc i inside
  exact ⟨value,vv,read coeff p i shared value hv⟩

theorem total (p : Prepared) (shared coefficient : Q)
    (vp : PV_CB_CanonicalPreparedCtor.Valid p)
    (vs : PV_CB_CanonicalTower.Valid shared) (vc : PV_CB_CanonicalTower.Valid coefficient) :
    ∃ out, scalar p shared coefficient = ok out ∧ PV_CB_CanonicalTower.Valid out := by
  obtain ⟨product,hp,vp⟩ := PV_CB_CanonicalPreparedMul.mul p shared vp vs
  obtain ⟨out,ho,vo⟩ := PV_CB_CanonicalQuartic.add product coefficient vp vc
  refine ⟨out,?_,vo⟩
  simpa only [scalar,PV_CB_MaskHorner.S.mul,PV_CB_MaskHorner.S.add,
    PV_CB_PreparedTotal.S.mul,PV_CB_CurrentQuartic.S.add,hp,ho,bind_tc_ok]
#print axioms representative
#print axioms total
end R1Z.PV_CB_HornerCanonicalCell
