import CompPoly.Univariate.Raw.Modular
import ExtractorPowComplexity
import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega

namespace ExtractorPowComplexity
open CompPoly
variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

def rawPowModWithCost (M : CPolynomial.Raw.MulContext F)
    (D : CPolynomial.Raw.ModContext F) (modulus : CPolynomial.Raw F) :
    Nat → CPolynomial.Raw F → CPolynomial.Raw F → CPolynomial.Raw F × Nat
  | 0, acc, _ => (acc, 0)
  | n + 1, acc, current =>
      let doAcc := (n + 1) % 2 == 1
      let acc' := if doAcc then CPolynomial.Raw.mulModWith M D modulus acc current else acc
      let current' := CPolynomial.Raw.mulModWith M D modulus current current
      let tail := rawPowModWithCost M D modulus ((n + 1) / 2) acc' current'
      (tail.1, (if doAcc then 1 else 0) + 1 + tail.2)
termination_by exponent _ _ => exponent
decreasing_by exact Nat.div_lt_self (Nat.succ_pos n) (by decide)

def powModWithCost (M : CPolynomial.Raw.MulContext F)
    (D : CPolynomial.Raw.ModContext F) (modulus base : CPolynomial.Raw F)
    (exponent : Nat) : CPolynomial.Raw F × Nat :=
  let oneMod :=
    if modulus.trim == 0 then (1 : CPolynomial.Raw F)
    else D.modByMonic (1 : CPolynomial.Raw F) (CPolynomial.Raw.monicNormalize modulus)
  rawPowModWithCost M D modulus exponent oneMod base

theorem rawPowModWithCost_value_eq (M : CPolynomial.Raw.MulContext F)
    (D : CPolynomial.Raw.ModContext F) (modulus : CPolynomial.Raw F)
    (n : Nat) (acc current : CPolynomial.Raw F) :
    (rawPowModWithCost M D modulus n acc current).1 =
      CPolynomial.Raw.powModBinaryAuxWith M D modulus n acc current := by
  induction n using Nat.strong_induction_on generalizing acc current with
  | h n ih =>
      cases n with
      | zero => simp [rawPowModWithCost, CPolynomial.Raw.powModBinaryAuxWith]
      | succ k =>
          have hrec : (k + 1) / 2 < k + 1 :=
            Nat.div_lt_self (Nat.succ_pos k) (by decide)
          rw [rawPowModWithCost, CPolynomial.Raw.powModBinaryAuxWith]
          exact ih ((k + 1) / 2) hrec _ _

theorem rawPowModWithCost_le_log_bound (M : CPolynomial.Raw.MulContext F)
    (D : CPolynomial.Raw.ModContext F) (modulus : CPolynomial.Raw F)
    (n : Nat) (acc current : CPolynomial.Raw F) :
    (rawPowModWithCost M D modulus n acc current).2 ≤
      2 * (Nat.log2 n + 1) := by
  induction n using Nat.strong_induction_on generalizing acc current with
  | h n ih =>
      cases n with
      | zero => simp [rawPowModWithCost]
      | succ k =>
          by_cases hk : k = 0
          · subst k
            simp [rawPowModWithCost, Nat.log2_def]
          · have hsmall : 2 ≤ k + 1 := by omega
            have hrec : (k + 1) / 2 < k + 1 :=
              Nat.div_lt_self (Nat.succ_pos k) (by decide)
            have hi := ih ((k + 1) / 2) hrec
              (if (k + 1) % 2 == 1 then CPolynomial.Raw.mulModWith M D modulus acc current else acc)
              (CPolynomial.Raw.mulModWith M D modulus current current)
            rw [rawPowModWithCost, Nat.log2_def]
            simp only [if_pos hsmall]
            have hbit : (if (k + 1) % 2 == 1 then 1 else 0) ≤ 1 := by
              split <;> omega
            omega

theorem powModWithCost_value_eq (M : CPolynomial.Raw.MulContext F)
    (D : CPolynomial.Raw.ModContext F) (modulus base : CPolynomial.Raw F)
    (exponent : Nat) :
    (powModWithCost M D modulus base exponent).1 =
      CPolynomial.Raw.powModWith M D modulus base exponent := by
  unfold powModWithCost CPolynomial.Raw.powModWith
  exact rawPowModWithCost_value_eq M D modulus exponent _ _

theorem powModWithCost_le_log_bound (M : CPolynomial.Raw.MulContext F)
    (D : CPolynomial.Raw.ModContext F) (modulus base : CPolynomial.Raw F)
    (exponent : Nat) :
    (powModWithCost M D modulus base exponent).2 ≤
      2 * (Nat.log2 exponent + 1) := by
  unfold powModWithCost
  exact rawPowModWithCost_le_log_bound M D modulus exponent _ _

#print axioms powModWithCost_value_eq
#print axioms powModWithCost_le_log_bound
end ExtractorPowComplexity
