import PV_L2E_DivisionTrace
set_option autoImplicit false
namespace PV_L2E_Dividend
open PV_L2D_DivisionBounds

/-- The source forms the dividend with a shifted bitwise OR, not addition.
The low word bound establishes that these two operations agree. -/
theorem or_is_dividend (r x : Nat) (hx : x<B) :
    (r <<< 32 ||| x)=dividend r x := by
  rw [← Nat.shiftLeft_add_eq_or_of_lt (show x<2^32 from hx)]
  simp only [Nat.shiftLeft_eq,dividend,B]

theorem quotient_safe (r x : Nat) (hr : r<P) (hx : x<B) :
    (r <<< 32 ||| x)<2^64 ∧ (r <<< 32 ||| x)/P<B ∧
      (r <<< 32 ||| x)%P<P := by
  rw [or_is_dividend r x hx]
  exact ⟨(u64_safe r x hr hx).2,quotient_word r x hr hx,remainder_field r x⟩

/-- Both source casts are lossless on every admitted step. -/
theorem casts_lossless (r x : Nat) (hr : r<P) (hx : x<B) :
    ((r <<< 32 ||| x)/P)%B=(r <<< 32 ||| x)/P ∧
      ((r <<< 32 ||| x)%P)%B=(r <<< 32 ||| x)%P := by
  obtain ⟨_,hq,hm⟩ := quotient_safe r x hr hx
  exact ⟨Nat.mod_eq_of_lt hq,Nat.mod_eq_of_lt (lt_trans hm (by decide))⟩

#print axioms or_is_dividend
#print axioms quotient_safe
#print axioms casts_lossless
end PV_L2E_Dividend
