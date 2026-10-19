import CompPolyPolynomialBackendBridge
import Mathlib.Data.Nat.Size

/-! Step accounting for the exact `Nat.binaryRec` modular exponentiation
used by the extractor's split trial. This is not the separate Raw.powModWith
implementation. Coefficient-operation charges per step remain separate. -/
set_option autoImplicit false
namespace AspisR1.ActualExtractorModPowerSteps
open CompPoly CompPolyPolynomialBackendBridge
variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

def counted (a m : CPolynomial F) : Nat → CPolynomial F × Nat :=
  Nat.binaryRec (1,0) (fun b _ z =>
    ((z.1*z.1*(if b then a else 1)).modByMonic m,z.2+1))

theorem counted_value_steps (a m : CPolynomial F) (e : Nat) :
    (counted a m e).1 = modPower a m e ∧
      (counted a m e).2 = Nat.size e := by
  refine Nat.binaryRec (motive := fun n =>
    (counted a m n).1 = modPower a m n ∧ (counted a m n).2 = Nat.size n)
    ?_ ?_ e
  · simp [counted,modPower]
  · intro b n ih
    by_cases hz : Nat.bit b n = 0
    · rw [hz]
      simp [counted,modPower]
    · have hcond : n = 0 → b = true := by
        intro hn
        subst n
        cases b with
        | false => exact False.elim (hz rfl)
        | true => rfl
      unfold counted modPower
      rw [Nat.binaryRec_eq b n (Or.inr hcond),Nat.binaryRec_eq b n (Or.inr hcond)]
      change ((counted a m n).1*(counted a m n).1*(if b then a else 1)).modByMonic m =
          (modPower a m n * modPower a m n * (if b then a else 1)).modByMonic m ∧
        (counted a m n).2+1 = Nat.size (Nat.bit b n)
      constructor
      · rw [ih.1]
      · rw [ih.2,Nat.size_bit hz]

theorem exact_multiplication_sites (a m : CPolynomial F) (e : Nat) :
    2*(counted a m e).2 = 2*Nat.size e := by
  rw [(counted_value_steps a m e).2]

theorem exact_remainder_sites (a m : CPolynomial F) (e : Nat) :
    (counted a m e).2 = Nat.size e := (counted_value_steps a m e).2

#print axioms counted_value_steps
#print axioms exact_multiplication_sites
#print axioms exact_remainder_sites
end AspisR1.ActualExtractorModPowerSteps
