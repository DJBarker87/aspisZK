import F3U_RangeEdges
import F3U_RangeChord
set_option autoImplicit false
namespace AspisR1.F3U_Range
open F3U_RangePolynomial F3U_RangeEdges

theorem per_attempt (Q : Nat) (range : Q≤maxQueries) :
    F3T_Numeric.total Q≤(Q+1:Rat)*(1/(2:Rat)^100) := by
  have bound := F3U_RangeChord.chord maxQueries Q (by norm_num [maxQueries]) range edges.1 edges.2.1
  rw [←total_gap] at bound
  linarith

theorem next_fails : (maxQueries+2:Rat)*(1/(2:Rat)^100)<F3T_Numeric.total (maxQueries+1) := by
  have bad : 0<gap ((maxQueries+1:Nat):Rat) := by simpa only [Nat.cast_add,Nat.cast_one] using edges.2.2
  rw [←total_gap] at bad
  push_cast at bad
  linarith

#print axioms per_attempt
#print axioms next_fails
end AspisR1.F3U_Range
