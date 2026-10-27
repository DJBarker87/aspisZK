import R1Z.PV_CB_HornerCanonicalCell
set_option autoImplicit false
namespace R1Z.PV_CB_HornerScalarTransport
open Aeneas Aeneas.Std Result PV_CB_HornerCell

/-- A scalar gate need not carry27 unrelated coefficient variables.
    This lemma concerns retained control, not fresh shipped root association. -/
theorem lift (alternate : Prepared → Q → Q → Result Q)
    (agreement : ∀ p shared coefficient,
      PV_CB_CanonicalPreparedCtor.Valid p → PV_CB_CanonicalTower.Valid shared →
      PV_CB_CanonicalTower.Valid coefficient → scalar p shared coefficient = alternate p shared coefficient)
    (coeff : Coeff) (p : Prepared) (i : Usize) (shared : Q)
    (inside : i.val < 27) (vc : PV_CB_CanonicalArrays.Valid PV_CB_CanonicalTower.Valid coeff)
    (vp : PV_CB_CanonicalPreparedCtor.Valid p) (vs : PV_CB_CanonicalTower.Valid shared) :
    ∃ value, PV_CB_CanonicalTower.Valid value ∧ cell coeff p i shared = alternate p shared value := by
  obtain ⟨value,vv,h⟩ := PV_CB_HornerCanonicalCell.representative coeff p i shared inside vc
  exact ⟨value,vv,h.trans (agreement p shared value vp vs vv)⟩
#print axioms lift
end R1Z.PV_CB_HornerScalarTransport
