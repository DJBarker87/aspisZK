import Mathlib.Tactic
set_option autoImplicit false
namespace PV_L2C_InverseChain

def chain {M : Type} [Monoid M] (x : M) : M :=
  let t2 := (x*x)*x
  let t4 := t2^(2^2)*t2
  let t8 := t4^(2^4)*t4
  let t16 := t8^(2^8)*t8
  let t24 := t16^(2^8)*t8
  let t28 := t24^(2^4)*t4
  let t29 := (t28*t28)*x
  let t30 := t29*t29
  (t30*t30)*x

/-- The frozen 38-multiplication chain is checked symbolically; no concrete
field inverse or generated recurrence is normalized. -/
theorem exponent {M : Type} [Monoid M] (x : M) : chain x = x^2147483645 := by
  have h2 : (x*x)*x = x^3 := by simp [pow_succ]
  have h4 : (x^3)^(2^2)*x^3 = x^15 := by rw [← pow_mul,← pow_add]; norm_num
  have h8 : (x^15)^(2^4)*x^15 = x^255 := by rw [← pow_mul,← pow_add]; norm_num
  have h16 : (x^255)^(2^8)*x^255 = x^65535 := by rw [← pow_mul,← pow_add]; norm_num
  have h24 : (x^65535)^(2^8)*x^255 = x^16777215 := by rw [← pow_mul,← pow_add]; norm_num
  have h28 : (x^16777215)^(2^4)*x^15 = x^268435455 := by rw [← pow_mul,← pow_add]; norm_num
  have h29 : (x^268435455*x^268435455)*x = x^536870911 := by
    rw [← pow_add,← pow_succ]
  have h30 : x^536870911*x^536870911 = x^1073741822 := by rw [← pow_add]
  dsimp only [chain]
  rw [h2,h4,h8,h16,h24,h28,h29,h30,← pow_add,← pow_succ]
  norm_num
#print axioms exponent
end PV_L2C_InverseChain
