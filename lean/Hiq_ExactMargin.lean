import Hiq_Numeric
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hiq_ExactMargin

theorem new_term : Hiq_Numeric.accountLoss 0 - RawJ_Numeric.accountLoss 0 = 142224/(2:Rat)^256 := by
  rw [Hiq_Numeric.extra_loss]
  norm_num

theorem exact_margin :
    1/(2:Rat)^100 - Hiq_Numeric.total 0 =
      1/(2:Rat)^108 - 6*((1161:Rat)^2+2961^2)/(2:Rat)^256 -
      1/(2:Rat)^126 - 1/(2:Rat)^454 - 142224/(2:Rat)^256 := by
  rw [Hiq_Numeric.exact_zero_margin]
  congr 1
  norm_num

theorem positive_margin :
    1/(2:Rat)^109 < 1/(2:Rat)^100 - Hiq_Numeric.total 0 := by
  norm_num [Hiq_Numeric.total,Hiq_Numeric.accountLoss,PerAttemptEnvelope.B,BinPerQueryNumeric.power454]

#print axioms new_term
#print axioms exact_margin
#print axioms positive_margin
end AspisR1.Hiq_ExactMargin
end
