import R1Z.BuilderCanonical

/-! Withdrawal admission ignores the recipient owner/salt fields. Erasing
those unused fields preserves every original RspendPlus conjunct. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Src_WithdrawalRecipient
open R0P AspisR1.SpendRelation BuilderSpendRelation
variable {K : Type} [Field K] [DecidableEq K] [CharP K 2147483647]

def erase (w : Witness K) : Witness K :=
  {w with recipientOwner := fun _ => 0,recipientSalt := fun _ => 0}

theorem preserves (pub : Public K) (w : Witness K)
    (withdrawal : pub.variant = .withdrawal) (h : RspendPlus pub w) :
    RspendPlus pub (erase w) := by
  refine ⟨⟨h.1.1,h.1.2.1,h.1.2.2.1,h.1.2.2.2.1,?_,h.1.2.2.2.2.2⟩,h.2⟩
  simpa only [variantOutput,withdrawal,erase] using h.1.2.2.2.2.1

theorem lift_erase (w : Wspend) :
    BuilderCanonical.liftWitness (K := K) (erase w) =
      erase (BuilderCanonical.liftWitness (K := K) w) := by
  simp only [BuilderCanonical.liftWitness,erase,map_zero]

#print axioms preserves
#print axioms lift_erase
end R1Z.PV_Src_WithdrawalRecipient
