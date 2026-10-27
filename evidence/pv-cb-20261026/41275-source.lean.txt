import R1Z.PV_CB_HornerCoefficientPrefix
import R1Z.PV_CB_OwnedMaskHornerEq
set_option autoImplicit false
namespace R1Z.PV_CB_HornerPrefixControl
open Aeneas Aeneas.Std Result ProverRwSuccessReverseRange PV_CB_HornerCell

theorem retained (left right : Coeff) (p : Prepared) (e : Usize) (shared : Q)
    (agree : ∀ i : Usize, i.val < e.val → left.index_usize i = right.index_usize i) :
    PV_CB_MaskHorner.S.loop (before e) left p shared =
      PV_CB_MaskHorner.S.loop (before e) right p shared := by
  rw [PV_CB_MaskHorner.source left p e.val e shared rfl,
    PV_CB_MaskHorner.source right p e.val e shared rfl,
    PV_CB_HornerFiniteCells.source,PV_CB_HornerFiniteCells.source]
  exact PV_CB_HornerCoefficientPrefix.finite left right p e.val e shared rfl agree

theorem owned (left right : Coeff) (p : Prepared) (e : Usize) (shared : Q)
    (agree : ∀ i : Usize, i.val < e.val → left.index_usize i = right.index_usize i) :
    PV_CB_OwnedMask.owned.horner left p e shared =
      PV_CB_OwnedMask.owned.horner right p e shared := by
  rw [PV_CB_OwnedMaskHornerEq.source,PV_CB_OwnedMaskHornerEq.source]
  exact retained left right p e shared agree
#print axioms retained
#print axioms owned
end R1Z.PV_CB_HornerPrefixControl
