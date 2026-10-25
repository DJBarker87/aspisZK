import EndP_Numeric
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawJ_Numeric

/-- Account source envelope plus all canonical replay queries. -/
def accountLoss (Q : Nat) : Rat := 6*((Q+2961 : Nat) : Rat)^2/(2:Rat)^256

/-- Conservative comparison with EndP: retain its original frozen2 collision
term and both aborts, replacing only the old additional source-auth loss. -/
def total (Q : Nat) : Rat :=
  ((Q+34 : Nat) : Rat)*PerAttemptEnvelope.B +
    (6*((Q+1161 : Nat) : Rat)^2/(2:Rat)^256 + accountLoss Q) +
    1/(2:Rat)^126 + 1/(2:Rat)^454

theorem account_replay (Q : Nat) :
    6*((Q+1921+1040 : Nat) : Rat)^2/(256^32 : Rat) = accountLoss Q := by
  have power : (256^32 : Rat) = 2^256 := by
    calc
      (256^32 : Rat) = ((2^8)^32 : Rat) := rfl
      _ = (2^(8*32) : Rat) := (pow_mul 2 8 32).symm
      _ = (2^256 : Rat) := rfl
  rw [power]
  simp only [accountLoss,show Q+1921+1040 = Q+2961 by omega]

theorem zero_margin :
    1/(2:Rat)^100 - total 0 = 1/(2:Rat)^108 -
      6*((1161:Rat)^2+2961^2)/(2:Rat)^256 - 1/(2:Rat)^126 - 1/(2:Rat)^454 := by
  norm_num [total,accountLoss,PerAttemptEnvelope.B,BinPerQueryNumeric.power454]

theorem zero_queries : total 0 ≤ 1/(2:Rat)^100 := by
  norm_num [total,accountLoss,PerAttemptEnvelope.B,BinPerQueryNumeric.power454]

theorem margin_positive : 0 < 1/(2:Rat)^100 - total 0 := by
  norm_num [total,accountLoss,PerAttemptEnvelope.B,BinPerQueryNumeric.power454]

#print axioms account_replay
#print axioms zero_margin
#print axioms zero_queries
#print axioms margin_positive
end AspisR1.RawJ_Numeric
end
