import EndP_Numeric
set_option autoImplicit false
namespace AspisR1.F3T_Numeric

/-- Requested single account loss, charged once. Its source-event transport is
not established by the arithmetic definition or inequalities below. -/
def accountLoss (Q : Nat) : Rat := 6*((Q+2965 : Nat) : Rat)^2/(2:Rat)^256

def collisionLoss (Q : Nat) : Rat := 6*((Q+1161 : Nat) : Rat)^2/(2:Rat)^256

def total (Q : Nat) : Rat :=
  ((Q+34 : Nat) : Rat)*PerAttemptEnvelope.B + collisionLoss Q + accountLoss Q +
    1/(2:Rat)^126 + 1/(2:Rat)^454

/-- Positive spare margin, with both collisions and both aborts retained. -/
theorem margin_exact :
    1/(2:Rat)^100-total 0 =
    1/(2:Rat)^108 - 6*((1161:Rat)^2+2965^2)/(2:Rat)^256 -
      1/(2:Rat)^126 - 1/(2:Rat)^454 := by
  norm_num [total,collisionLoss,accountLoss,PerAttemptEnvelope.B,BinPerQueryNumeric.power454]

theorem margin_positive : 0 < 1/(2:Rat)^100-total 0 := by
  norm_num [total,collisionLoss,accountLoss,PerAttemptEnvelope.B,BinPerQueryNumeric.power454]

theorem zero_queries : total 0 < 1/(2:Rat)^100 := by
  exact sub_pos.mp margin_positive

#print axioms margin_exact
#print axioms margin_positive
#print axioms zero_queries
end AspisR1.F3T_Numeric
