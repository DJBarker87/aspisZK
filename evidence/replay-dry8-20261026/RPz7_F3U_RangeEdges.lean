import RPz7_F3U_RangePolynomial
set_option autoImplicit false
namespace AspisR1.F3U_RangeEdges
open F3U_RangePolynomial

def maxQueries : Nat := 7388980242446479800895501321004157112314840375

theorem edges : gap 0≤0 ∧ gap maxQueries≤0 ∧ 0<gap (maxQueries+1) := by
  norm_num [gap,maxQueries,BinPerQueryNumeric.power454]

#print axioms edges
end AspisR1.F3U_RangeEdges
