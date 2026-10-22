import R1Z.SimCostFixedOperations

/-! Explicit WideExact arithmetic on the actual eight-coordinate carrier.
This is an alternative arithmetic implementation in the retained primitive
RAM model, not a Rust instruction-count or shipped arithmetic refinement.
No new primitive tariff is postulated. Two result-coordinate stores cost 2.
Inversion uses bounded binary powering, including the total inverse at zero. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.SimCostWide5
open AspisWideTower AspisV8R15.ExactTowerBase R1Z.SimCostWriter
open R1Z.SimCostFixedOperations

def addRun (p : WideExact × WideExact) : Costed WideExact :=
  bind (qm31Add.run (p.1.re,p.2.re)) fun a =>
  bind (qm31Add.run (p.1.im,p.2.im)) fun b => (⟨a,b⟩,2)

theorem add_erase (p : WideExact × WideExact) : (addRun p).1 = p.1+p.2 := rfl

theorem add_cost (p : WideExact × WideExact) : (addRun p).2 = 10 := rfl

def add : Stage (fun p : WideExact × WideExact => p.1+p.2) 10 where
  run := addRun
  erase := add_erase
  bound p := (add_cost p).le

/-- Schoolbook outer quadratic multiplication: five QM31 multiplications,
two QM31 additions, and two stores. In particular this is NOT a QM31 tariff
assigned to multiplication on WideExact. -/
def mulRun (p : WideExact × WideExact) : Costed WideExact :=
  bind (qm31Mul.run (p.1.re,p.2.re)) fun ac =>
  bind (qm31Mul.run (p.1.im,p.2.im)) fun bd =>
  bind (qm31Mul.run (wideU,bd)) fun ubd =>
  bind (qm31Mul.run (p.1.re,p.2.im)) fun ad =>
  bind (qm31Mul.run (p.1.im,p.2.re)) fun bc =>
  bind (qm31Add.run (ac,ubd)) fun re =>
  bind (qm31Add.run (ad,bc)) fun im => (⟨re,im⟩,2)

theorem mul_erase (p : WideExact × WideExact) : (mulRun p).1 = p.1*p.2 := by
  simp only [mulRun, erase_bind, qm31Mul, qm31Add]
  apply QuadraticAlgebra.ext <;> simp only [QuadraticAlgebra.re_mul,
    QuadraticAlgebra.im_mul, zero_mul, add_zero, mul_assoc]

theorem mul_cost (p : WideExact × WideExact) : (mulRun p).2 = 170 := by
  simp only [mulRun, cost_bind, qm31Mul, qm31Add, tariff]

def mul : Stage (fun p : WideExact × WideExact => p.1*p.2) 170 where
  run := mulRun
  erase := mul_erase
  bound p := (mul_cost p).le

/-- Exactly k binary positions; the input exponent is public, and arithmetic
uses the supplied primitive composition. Each position includes three control
and assembly ticks, even on the branch omitting the extra product. -/
def power : Nat → WideExact → Nat → Costed WideExact
  | 0, _, _ => (1,1)
  | k+1, z, n =>
    bind (power k z (n/2)) fun half =>
    bind (mul.run (half,half)) fun square =>
    if n%2=0 then (square,3) else
      bind (mul.run (square,z)) fun out => (out,3)

theorem power_erase (k : Nat) (z : WideExact) (n : Nat) (hn : n < 2^k) :
    (power k z n).1 = z^n := by
  induction k generalizing n with
  | zero =>
    have hn0 : n=0 := by simpa using hn
    subst n
    rfl
  | succ k ih =>
    have hhalf : n/2 < 2^k := by
      rw [pow_succ] at hn
      omega
    simp only [power, erase_bind, mul.erase, ih _ hhalf]
    split_ifs with he
    · rw [← pow_add]
      have hnEq : n/2+n/2=n := by omega
      rw [hnEq]
    · simp only [erase_bind, mul.erase]
      rw [← pow_add, ← pow_succ]
      have hm := Nat.mod_lt n (by omega : 0<2)
      have hnEq : n/2+n/2+1=n := by omega
      rw [hnEq]

theorem power_bound (k : Nat) (z : WideExact) (n : Nat) :
    (power k z n).2 ≤ 343*k+1 := by
  induction k generalizing n with
  | zero => simp [power]
  | succ k ih =>
    have hh := ih (n/2)
    simp only [power, cost_bind]
    split_ifs <;> simp only [cost_bind, mul, mul_cost] <;> omega

/-- Fermat exponent on the actual field: no enumeration of its elements. -/
def inverseExponent : Nat := 2147483647^8-2

theorem inverse_exponent_bound : inverseExponent < 2^248 := by
  norm_num [inverseExponent]

theorem inverse_power (z : WideExact) : z^inverseExponent = z⁻¹ := by
  by_cases hz : z=0
  · subst z
    have hp : 0 < inverseExponent := by norm_num [inverseExponent]
    rw [zero_pow (Nat.ne_of_gt hp), inv_zero]
  · apply mul_left_cancel₀ hz
    rw [mul_inv_cancel₀ hz, ← pow_succ']
    have he : inverseExponent+1 = Fintype.card WideExact-1 := by
      rw [wideExact_card]
      norm_num [inverseExponent, P]
    rw [he]
    exact FiniteField.pow_card_sub_one_eq_one z hz

def invRun (z : WideExact) : Costed WideExact := power 248 z inverseExponent

theorem inv_erase (z : WideExact) : (invRun z).1 = z⁻¹ :=
  (power_erase 248 z inverseExponent inverse_exponent_bound).trans (inverse_power z)

theorem inv_bound (z : WideExact) : (invRun z).2 ≤ 85065 := by
  exact power_bound 248 z inverseExponent

def inv : Stage (fun z : WideExact => z⁻¹) 85065 where
  run := invRun
  erase := inv_erase
  bound := inv_bound

#print axioms add_erase
#print axioms add_cost
#print axioms mul_erase
#print axioms mul_cost
#print axioms power_erase
#print axioms power_bound
#print axioms inverse_exponent_bound
#print axioms inverse_power
#print axioms inv_erase
#print axioms inv_bound
end R1Z.SimCostWide5
