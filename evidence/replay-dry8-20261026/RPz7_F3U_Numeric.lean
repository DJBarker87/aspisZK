import RPz7_F3T_Numeric
set_option autoImplicit false
namespace AspisR1.F3U_Numeric

def margin : Rat := 1/(2:Rat)^108-6*((1161:Rat)^2+2965^2)/(2:Rat)^256-
  1/(2:Rat)^126-1/(2:Rat)^454

theorem exact : 1/(2:Rat)^100-F3T_Numeric.total 0=margin := F3T_Numeric.margin_exact

theorem positive : 0<margin := by rw [←exact];exact F3T_Numeric.margin_positive

theorem runtime_margin (failure : Rat) (bound : failure≤F3T_Numeric.total 0) :
    margin≤1/(2:Rat)^100-failure ∧ failure<1/(2:Rat)^100 := by
  constructor
  · rw [←exact];linarith
  · exact bound.trans_lt F3T_Numeric.zero_queries

#print axioms exact
#print axioms positive
#print axioms runtime_margin
end AspisR1.F3U_Numeric
