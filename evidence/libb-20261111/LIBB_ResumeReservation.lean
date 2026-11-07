import LIBB_Tx2Reservation
import NNC_ResumeEvents
set_option autoImplicit false
noncomputable section
namespace LIBB_ResumeReservation
open AspisR1
/-- The frozen resume path observes only the reservation tag. No Err payload
or allocation-success premise is introduced by this normalization. -/
theorem filled (a b : NP6_StdModel.Reservation)
 (h : NJC_FilledClause.reserved a = NJC_FilledClause.reserved b) :
 @NJU_ResumeObserved.recordFilled a = @NJU_ResumeObserved.recordFilled b := by
 unfold NJU_ResumeObserved.recordFilled
 rw [h]

theorem tail (a b : NP6_StdModel.Reservation)
 (h : NJC_FilledClause.reserved a = NJC_FilledClause.reserved b) :
 @NJU_ResumeObserved.finishTailG a = @NJU_ResumeObserved.finishTailG b := by
 unfold NJU_ResumeObserved.finishTailG
 rw [filled a b h]

theorem endBlock (a b : NP6_StdModel.Reservation)
 (h : NJC_FilledClause.reserved a = NJC_FilledClause.reserved b) :
 @NJU_ResumeObserved.queryEndG a = @NJU_ResumeObserved.queryEndG b := by
 unfold NJU_ResumeObserved.queryEndG
 rw [tail a b h]

theorem middle (a b : NP6_StdModel.Reservation)
 (h : NJC_FilledClause.reserved a = NJC_FilledClause.reserved b) :
 @NJU_ResumeObserved.queryMidG a = @NJU_ResumeObserved.queryMidG b := by
 unfold NJU_ResumeObserved.queryMidG
 rw [endBlock a b h]

theorem query (a b : NP6_StdModel.Reservation)
 (h : NJC_FilledClause.reserved a = NJC_FilledClause.reserved b) :
 @NJU_ResumeObserved.queryBlockG a = @NJU_ResumeObserved.queryBlockG b := by
 unfold NJU_ResumeObserved.queryBlockG
 rw [middle a b h]

theorem body (a b : NP6_StdModel.Reservation)
 (h : NJC_FilledClause.reserved a = NJC_FilledClause.reserved b) :
 @NJU_ResumeObserved.resumeBodyG a = @NJU_ResumeObserved.resumeBodyG b := by
 unfold NJU_ResumeObserved.resumeBodyG
 rw [query a b h]

theorem run (a b : NP6_StdModel.Reservation)
 (h : NJC_FilledClause.reserved a = NJC_FilledClause.reserved b) :
 @NJU_ResumeObserved.run a = @NJU_ResumeObserved.run b := by
 unfold NJU_ResumeObserved.run
 rw [body a b h]
#print axioms filled
#print axioms tail
#print axioms endBlock
#print axioms middle
#print axioms query
#print axioms body
#print axioms run
end LIBB_ResumeReservation
end
