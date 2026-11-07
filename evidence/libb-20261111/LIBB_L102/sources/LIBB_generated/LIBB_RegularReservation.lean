import LIBB_DenseReservation
set_option autoImplicit false
noncomputable section
namespace LIBB_RegularReservation
open AspisR1
/-- Only the nested dense child uses the allocation instance. -/
theorem kind (a b : NP6_StdModel.Reservation)
 (h : NJC_FilledClause.reserved a = NJC_FilledClause.reserved b) :
 @FIo_Native.weights.process_kind (FIo_Install.allocation a) =
 @FIo_Native.weights.process_kind (FIo_Install.allocation b) := by
 unfold FIo_Native.weights.process_kind
 rw [LIBB_DenseReservation.emitted a b h]

theorem regular (a b : NP6_StdModel.Reservation)
 (h : NJC_FilledClause.reserved a = NJC_FilledClause.reserved b) :
 @FIo_Native.weights.process_regular_kinds (FIo_Install.allocation a) =
 @FIo_Native.weights.process_regular_kinds (FIo_Install.allocation b) := by
 unfold FIo_Native.weights.process_regular_kinds
 rw [kind a b h]
#print axioms kind
#print axioms regular
end LIBB_RegularReservation
end
