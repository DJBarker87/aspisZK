import NBL_AddNative
import R1SamplerAddBridge
set_option autoImplicit false
namespace AspisR1.NBL_SecondCarry
open SamplerAddDigits SamplerAddBridge

/-- General end-around-carry safety, independent of a concrete numeral or
recurrence evaluation. A positive first carry makes the next increment fit. -/
theorem natural {p a : Nat} (hp : 0<p) (xs : List Nat)
    (canonical : ∀ d∈xs,d<p) (small : a<p^xs.length)
    (wrapped : 0<(addDigits p a xs).2) :
    (addDigits p 1 (addDigits p a xs).1).2=0 := by
  have bounded := digitsValue_lt_pow hp xs canonical
  have first := addDigits_mod_div hp a xs
  have ge : p^xs.length≤digitsValue p xs+a := by
    by_contra h
    have zero : (digitsValue p xs+a)/p^xs.length=0 := Nat.div_eq_of_lt (by omega)
    rw [first.2,zero] at wrapped
    omega
  have lt : digitsValue p xs+a<2*p^xs.length := by omega
  have remainder : (digitsValue p xs+a)%p^xs.length=digitsValue p xs+a-p^xs.length := by
    rw [Nat.mod_eq_sub_mod ge,Nat.mod_eq_of_lt (by omega)]
  have next := (addDigits_mod_div hp 1 (addDigits p a xs).1).2
  rw [addDigits_length,first.1,remainder] at next
  rw [next]
  exact Nat.div_eq_of_lt (by omega)

#print axioms natural
end AspisR1.NBL_SecondCarry
