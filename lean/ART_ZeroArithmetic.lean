import ART_StartCharge
set_option autoImplicit false
namespace AspisR1.ART_ZeroArithmetic

/-- Exact retained margin, including both collision terms and abort terms. -/
theorem margin : 1/(2:Rat)^100-F3T_Numeric.total 0 =
    1/(2:Rat)^108-6*((1161:Rat)^2+2965^2)/(2:Rat)^256-
      1/(2:Rat)^126-1/(2:Rat)^454 := F3T_Numeric.margin_exact

theorem positive : F3T_Numeric.total 0 < 1/(2:Rat)^100 := F3T_Numeric.zero_queries

/-- If TWO independently charged transcript failures were union-bounded,
68 starts alone would already exceed the zero-query target. This is not the
one-first-transcript event in ARQ's recovery theorem. -/
theorem doubled_shortfall :
    (68:Rat)*PerAttemptEnvelope.B-1/(2:Rat)^100 = (127:Rat)/2^107 := by
  norm_num [PerAttemptEnvelope.B,BinPerQueryNumeric.power454]

theorem first_fraction : (34:Rat)*PerAttemptEnvelope.B/(1/(2:Rat)^100) = (255:Rat)/256 := by
  norm_num [PerAttemptEnvelope.B,BinPerQueryNumeric.power454]

#print axioms margin
#print axioms positive
#print axioms doubled_shortfall
#print axioms first_fraction
end AspisR1.ART_ZeroArithmetic
