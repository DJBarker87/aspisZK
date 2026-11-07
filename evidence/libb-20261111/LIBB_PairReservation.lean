import LIBB_RegularReservation
set_option autoImplicit false
noncomputable section
namespace LIBB_PairReservation
open Aeneas Aeneas.Std Result AspisR1
/-- Normalize the outer and nested dense reservations; keep loops opaque. -/
theorem emitted (a b : NP6_StdModel.Reservation)
 (h : NJC_FilledClause.reserved a = NJC_FilledClause.reserved b) :
 @FIo_Native.weights.Weights.pair (FIo_Install.allocation a) =
 @FIo_Native.weights.Weights.pair (FIo_Install.allocation b) := by
 funext owner alpha message kappa
 unfold FIo_Native.weights.Weights.pair
 simp only [NHI_FilledModel.qm, LIBB_DenseReservation.reply a b h,
  LIBB_RegularReservation.regular a b h]

theorem installed (a b : NP6_StdModel.Reservation)
 (h : NJC_FilledClause.reserved a = NJC_FilledClause.reserved b) :
 FIo_Install.pair a = FIo_Install.pair b := by
 unfold FIo_Install.pair
 rw [emitted a b h]

theorem slots (a b : NP6_StdModel.Reservation)
 (h : NJC_FilledClause.reserved a = NJC_FilledClause.reserved b) :
 IDa_Deployed.finish a = IDa_Deployed.finish b := by
 unfold IDa_Deployed.finish
 rw [installed a b h]

theorem finish (a b : NP6_StdModel.Reservation)
 (h : NJC_FilledClause.reserved a = NJC_FilledClause.reserved b) :
 NLB_Parent.finish a = NLB_Parent.finish b := by
 unfold NLB_Parent.finish NIG_Slots.installed
 rw [slots a b h]
#print axioms emitted
#print axioms installed
#print axioms slots
#print axioms finish
end LIBB_PairReservation
end
