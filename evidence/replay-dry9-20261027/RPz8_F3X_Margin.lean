import RPz8_F3U_Numeric
set_option autoImplicit false
namespace AspisR1.F3X_Margin

/-- Independent recheck of the adopted headline arithmetic, including both
collision charges and both abort terms. These are per-attempt constants. -/
theorem exact :
    1/(2:Rat)^100-F3T_Numeric.total 0=
      1/(2:Rat)^108-6*((1161:Rat)^2+2965^2)/(2:Rat)^256-
        1/(2:Rat)^126-1/(2:Rat)^454 := by
  norm_num [F3T_Numeric.total,F3T_Numeric.collisionLoss,F3T_Numeric.accountLoss,
    PerAttemptEnvelope.B,BinPerQueryNumeric.power454]

theorem positive :
    0<1/(2:Rat)^108-6*((1161:Rat)^2+2965^2)/(2:Rat)^256-
      1/(2:Rat)^126-1/(2:Rat)^454 := by
  norm_num [BinPerQueryNumeric.power454]

theorem headline_zero : F3T_Numeric.total 0<1/(2:Rat)^100 := by
  apply sub_pos.mp
  rw [AspisR1.F3X_Margin.exact]
  exact positive

#print axioms exact
#print axioms positive
#print axioms headline_zero
end AspisR1.F3X_Margin
