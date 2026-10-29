import R1Z.PV_RDCD3_CB_OwnedMaskHorner
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RDCD3_CB_OwnedMaskHornerEq
open Aeneas Aeneas.Std Result PV_RDCD3_ReverseRange
abbrev Q := ProverRwFull.aspis_core.field.QM31
theorem source (coeff : Array Q 27#usize) (p : PV_RDCD3_CB_PreparedTotal.Prepared)
    (e : Usize) (shared : Q) :
    PV_RDCD3_CB_OwnedMask.owned.horner coeff p e shared =
    PV_RDCD3_CB_MaskHorner.S.loop (before e) coeff p shared := by
  exact (PV_RDCD3_CB_OwnedMaskHorner.source coeff p e.val e shared rfl).trans
    (PV_RDCD3_CB_MaskHorner.source coeff p e.val e shared rfl).symm
#print axioms source
end R1Z.PV_RDCD3_CB_OwnedMaskHornerEq
