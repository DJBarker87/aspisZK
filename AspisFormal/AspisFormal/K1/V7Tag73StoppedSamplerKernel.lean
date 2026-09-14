import AspisFormal.K1.V7Tag73FiniteSubkernel

/-!
# First-success decoder laws without conditioning on later verifier acceptance

Every raw attempt is sampled from the specified kernel. Rejected decodes
consume attempts and have mass `rejectMass`. The helper is generic so the
actual bounded-retry QM31 decoder can instantiate it only AFTER its precise
raw-block consumption is connected to the native scheduler.
-/
set_option autoImplicit false
namespace AspisK1.V7Tag73StoppedSamplerKernel
open scoped BigOperators
open AspisK1.V7Tag73FiniteSubkernel
noncomputable section
variable {Raw Value : Type*} [Fintype Raw] [DecidableEq Value]

def rejectMass (w : Raw → ENNReal) (decode : Raw → Option Value) : ENNReal :=
  eventMass w (fun a => decode a = none)

/-- Unnormalised probability of returning one particular value by retry cap. -/
def firstSuccessAtom (w : Raw → ENNReal) (decode : Raw → Option Value)
    (value : Value) : Nat → ENNReal
  | 0 => 0
  | n + 1 => decodedAtomMass w decode value +
      rejectMass w decode * firstSuccessAtom w decode value n

/-- Complete exhaustion is retained separately, not redistributed to values. -/
def exhaustionMass (w : Raw → ENNReal) (decode : Raw → Option Value) : Nat → ENNReal
  | 0 => 1
  | n + 1 => rejectMass w decode * exhaustionMass w decode n

theorem exhaustionMass_eq_pow (w : Raw → ENNReal) (decode : Raw → Option Value)
    (n : Nat) : exhaustionMass w decode n = rejectMass w decode ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [exhaustionMass, ih, pow_succ, mul_comm]

/-- A division-free geometric coefficient is safe at rejectMass = 1. -/
def geometricWeight (r : ENNReal) : Nat → ENNReal
  | 0 => 0
  | n + 1 => 1 + r * geometricWeight r n

theorem firstSuccessAtom_factor (w : Raw → ENNReal) (decode : Raw → Option Value)
    (value : Value) (n : Nat) :
    firstSuccessAtom w decode value n =
      decodedAtomMass w decode value * geometricWeight (rejectMass w decode) n := by
  induction n with
  | zero => simp [firstSuccessAtom, geometricWeight]
  | succ n ih =>
      simp only [firstSuccessAtom, geometricWeight, ih, mul_add, mul_one]
      ac_rfl

theorem geometricWeight_eq_sum (r : ENNReal) (n : Nat) :
    geometricWeight r n = ∑ i ∈ Finset.range n, r ^ i := by
  induction n with
  | zero => simp [geometricWeight]
  | succ n ih =>
      rw [geometricWeight, ih]
      rw [Finset.sum_range_succ']
      simp only [pow_zero, pow_succ', Finset.mul_sum]
      ac_rfl

theorem geometricWeight_le_cap (r : ENNReal) (hr : r ≤ 1) (n : Nat) :
    geometricWeight r n ≤ (n : ENNReal) := by
  induction n with
  | zero => simp [geometricWeight]
  | succ n ih =>
      calc
        geometricWeight r (n + 1) = 1 + r * geometricWeight r n := rfl
        _ ≤ 1 + 1 * (n : ENNReal) := add_le_add le_rfl (mul_le_mul' hr ih)
        _ = ((n + 1 : Nat) : ENNReal) := by simp [add_comm]

/-- Bounded retry amplification, not an unjustified exact-uniform claim. -/
theorem firstSuccessAtom_le (w : Raw → ENNReal) (decode : Raw → Option Value)
    (value : Value) (atomCap : ENNReal)
    (atomBound : decodedAtomMass w decode value ≤ atomCap)
    (rejectBound : rejectMass w decode ≤ 1) (n : Nat) :
    firstSuccessAtom w decode value n ≤ atomCap * (n : ENNReal) := by
  rw [firstSuccessAtom_factor]
  exact mul_le_mul' atomBound (geometricWeight_le_cap _ rejectBound n)

/-- All values have the same multiplier if their one-attempt atoms do.
This is an unnormalised equality and says nothing about acceptance filtering. -/
theorem equal_atoms_stay_equal (w : Raw → ENNReal)
    (decode : Raw → Option Value) (left right : Value)
    (same : decodedAtomMass w decode left = decodedAtomMass w decode right)
    (n : Nat) : firstSuccessAtom w decode left n = firstSuccessAtom w decode right n := by
  rw [firstSuccessAtom_factor, firstSuccessAtom_factor, same]

/-- No attempt and no accepted value means exhaustion has probability one. -/
theorem zero_cap_has_full_exhaustion (w : Raw → ENNReal)
    (decode : Raw → Option Value) : exhaustionMass w decode 0 = 1 := rfl

#print axioms exhaustionMass_eq_pow
#print axioms firstSuccessAtom_factor
#print axioms geometricWeight_le_cap
#print axioms firstSuccessAtom_le
#print axioms equal_atoms_stay_equal
end
end AspisK1.V7Tag73StoppedSamplerKernel
