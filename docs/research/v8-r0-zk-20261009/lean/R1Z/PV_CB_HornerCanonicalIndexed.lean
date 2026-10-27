import R1Z.PV_CB_HornerCanonicalCell
set_option autoImplicit false
namespace R1Z.PV_CB_HornerCanonicalIndexed
open Aeneas Aeneas.Std Result PV_CB_HornerCell

theorem cell (coeff : Coeff) (p : Prepared) (i : Usize) (shared : Q)
    (inside : i.val < 27) (vc : PV_CB_CanonicalArrays.Valid PV_CB_CanonicalTower.Valid coeff)
    (vp : PV_CB_CanonicalPreparedCtor.Valid p) (vs : PV_CB_CanonicalTower.Valid shared) :
    ∃ out, PV_CB_HornerCell.cell coeff p i shared = ok out ∧ PV_CB_CanonicalTower.Valid out := by
  obtain ⟨value,vv,hv⟩ := PV_CB_HornerCanonicalCell.representative coeff p i shared inside vc
  obtain ⟨out,ho,vo⟩ := PV_CB_HornerCanonicalCell.total p shared value vp vs vv
  exact ⟨out,hv.trans ho,vo⟩
#print axioms cell
end R1Z.PV_CB_HornerCanonicalIndexed
