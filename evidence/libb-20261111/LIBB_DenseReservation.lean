import LIBB_Tx2Reservation
import NLT_NativeSource
import NHI_FilledModel
set_option autoImplicit false
noncomputable section
namespace LIBB_DenseReservation
open Aeneas Aeneas.Std Result AspisR1
theorem reply (a b : NP6_StdModel.Reservation)
 (h : NJC_FilledClause.reserved a = NJC_FilledClause.reserved b)
 {T : Type} (n : Usize) (value : T) :
 NHI_FilledModel.result a n value = NHI_FilledModel.result b n value := by
 cases a with
 | Err ea => cases b with
   | Err eb => rfl
   | Ok ub => cases ub; cases h
 | Ok ua => cases ua; cases b with
   | Err eb => cases h
   | Ok ub => cases ub; rfl

/-- Isolate the nested dense-point reservation; keep all loops opaque. -/
theorem emitted (a b : NP6_StdModel.Reservation)
 (h : NJC_FilledClause.reserved a = NJC_FilledClause.reserved b) :
 @FIo_Native.weights.Weights.dense_point_pair (FIo_Install.allocation a) =
 @FIo_Native.weights.Weights.dense_point_pair (FIo_Install.allocation b) := by
 funext owner kind alpha message
 unfold FIo_Native.weights.Weights.dense_point_pair
 simp only [NHI_FilledModel.qm,reply a b h]
#print axioms reply
#print axioms emitted
end LIBB_DenseReservation
end
