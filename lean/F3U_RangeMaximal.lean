import F3U_Range
set_option autoImplicit false
namespace AspisR1.F3U_RangeMaximal
open F3U_RangePolynomial F3U_RangeEdges

theorem beyond (Q : Nat) (above : maxQueries<Q) :
    (Q+1:Rat)*(1/(2:Rat)^100)<F3T_Numeric.total Q := by
  have positive : 0<gap (Q:Rat) := by
    by_contra notPositive
    have bounded : gap (Q:Rat)≤0 := le_of_not_gt notPositive
    have next := F3U_RangeChord.chord Q (maxQueries+1) (by omega) (by omega) edges.1 bounded
    have bad : 0<gap ((maxQueries+1:Nat):Rat) := by
      simpa only [Nat.cast_add,Nat.cast_one] using edges.2.2
    exact (not_le_of_gt bad) next
  rw [←total_gap] at positive
  linarith

theorem exact_range (Q : Nat) :
    F3T_Numeric.total Q≤(Q+1:Rat)*(1/(2:Rat)^100) ↔ Q≤maxQueries := by
  constructor
  · intro bound
    by_contra above
    exact (not_le_of_gt (beyond Q (by omega))) bound
  · exact F3U_Range.per_attempt Q

#print axioms beyond
#print axioms exact_range
end AspisR1.F3U_RangeMaximal
