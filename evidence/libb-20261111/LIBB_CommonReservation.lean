import LIBB_PairReservation
set_option autoImplicit false
noncomputable section
namespace LIBB_CommonReservation
open AspisR1

theorem resume (a b : NP6_StdModel.Reservation)
 (h : NJC_FilledClause.reserved a = NJC_FilledClause.reserved b) :
 @NJJ_Common.resume a = @NJJ_Common.resume b := by
 unfold NJJ_Common.resume
 rw [h]

theorem pending (a b : NP6_StdModel.Reservation)
 (h : NJC_FilledClause.reserved a = NJC_FilledClause.reserved b) :
 NJJ_Common.pending a = NJJ_Common.pending b := by
 unfold NJJ_Common.pending
 rw [h]

theorem source (a a' b b' c c' : NP6_StdModel.Reservation) (merkle : NJJ_Common.Merkle)
 (ha : NJC_FilledClause.reserved a = NJC_FilledClause.reserved a')
 (hb : NJC_FilledClause.reserved b = NJC_FilledClause.reserved b')
 (hc : NJC_FilledClause.reserved c = NJC_FilledClause.reserved c') :
 @NJJ_Common.run a b merkle (NLB_Parent.finish c) =
 @NJJ_Common.run a' b' merkle (NLB_Parent.finish c') := by
 unfold NJJ_Common.run
 rw [resume a a' ha,pending b b' hb,LIBB_PairReservation.finish c c' hc]

theorem observed (a a' b b' c c' : NP6_StdModel.Reservation) (merkle : NJJ_Common.Merkle)
 (ha : NJC_FilledClause.reserved a = NJC_FilledClause.reserved a')
 (hb : NJC_FilledClause.reserved b = NJC_FilledClause.reserved b')
 (hc : NJC_FilledClause.reserved c = NJC_FilledClause.reserved c') :
 @NJU_CommonObserved.run a b merkle (NLB_Parent.finish c) =
 @NJU_CommonObserved.run a' b' merkle (NLB_Parent.finish c') := by
 unfold NJU_CommonObserved.run
 rw [resume a a' ha,pending b b' hb,LIBB_PairReservation.finish c c' hc]
#print axioms resume
#print axioms pending
#print axioms source
#print axioms observed
end LIBB_CommonReservation
end
