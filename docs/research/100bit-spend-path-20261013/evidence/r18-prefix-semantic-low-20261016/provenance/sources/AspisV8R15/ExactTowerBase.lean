import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Tactic.NormNum.Prime

/-! Minimal retained tower, extracted verbatim from declarations in
AspisFormal/V5ComponentCQM31TowerExact.lean (SHA-256
75404d16b5a71f67146b91ca35739b111f81bb730beb77432267f2b5385cebe5).
Only namespace/imports change; the existing 30-step certificate is reused.
No sampler or probability capstone imports are needed for circle algebra. -/
set_option maxRecDepth 20000
namespace AspisV8R15.ExactTowerBase
abbrev P : Nat := 2147483647

instance m31PrimeFact : Fact P.Prime := ⟨by norm_num [P]⟩

/-- The exact mathematical M31 field. -/
abbrev M31Exact := ZMod P

/-- `-1` is not a square modulo the deployed Mersenne prime. -/
theorem m31_neg_one_not_isSquare : ¬ IsSquare (-1 : M31Exact) := by
  rw [ZMod.exists_sq_eq_neg_one_iff]
  norm_num [P]

/-- One square-and-multiply step for the exponent recurrence
`e_(k+1)=2*e_k+1`. -/
def fivePowStep (z : M31Exact) : M31Exact := z * z * 5

/-- Thirty iterations compute exponent `2^30-1`, using only thirty concrete
field squarings/multiplications in the kernel. -/
theorem fivePowStep_iterate (k : Nat) :
    fivePowStep^[k] 1 = (5 : M31Exact) ^ (2 ^ k - 1) := by
  induction k with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ', Function.comp_apply, ih]
      unfold fivePowStep
      calc
        (5 : M31Exact) ^ (2 ^ n - 1) * 5 ^ (2 ^ n - 1) * 5 =
            5 ^ ((2 ^ n - 1) + (2 ^ n - 1)) * 5 := by rw [pow_add]
        _ = 5 ^ ((2 ^ n - 1) + (2 ^ n - 1) + 1) := by
          simpa using
            (pow_add (5 : M31Exact)
              ((2 ^ n - 1) + (2 ^ n - 1)) 1).symm
        _ = 5 ^ (2 ^ (n + 1) - 1) := by
          congr 1
          rw [pow_succ]
          have hp : 1 ≤ 2 ^ n := Nat.one_le_two_pow
          omega

/-- The concrete Euler certificate: `5^(P/2) != 1`. -/
theorem five_euler_certificate : (5 : M31Exact) ^ (P / 2) ≠ 1 := by
  rw [show P / 2 = 2 ^ 30 - 1 by norm_num [P], ← fivePowStep_iterate 30]
  decide

/-- `5` is not a square modulo `P`, by Euler's criterion and the kernel-checked
30-step certificate above. -/
theorem m31_five_not_isSquare : ¬ IsSquare (5 : M31Exact) := by
  rw [ZMod.euler_criterion P (by decide)]
  exact five_euler_certificate

/-- Exact deployed complex extension: `i^2 = -1`. -/
abbrev CM31Exact := QuadraticAlgebra M31Exact (-1) 0

instance cm31Rootless : Fact
    (∀ r : M31Exact, r ^ 2 ≠ (-1 : M31Exact) + 0 * r) := ⟨by
  intro r hr
  apply m31_neg_one_not_isSquare
  refine ⟨r, ?_⟩
  simpa [pow_two] using hr.symm
⟩

/-- The literal non-residue `R = 2+i` from the Rust source. -/
def qm31R : CM31Exact := ⟨2, 1⟩

@[simp] theorem qm31R_re : qm31R.re = 2 := rfl
@[simp] theorem qm31R_im : qm31R.im = 1 := rfl

theorem cm31_norm_qm31R : QuadraticAlgebra.norm qm31R = (5 : M31Exact) := by
  norm_num [qm31R, QuadraticAlgebra.norm_def]

/-- `2+i` is a nonsquare in CM31: the norm of a square is a square, while
`Norm(2+i)=5` is a nonsquare in M31. -/
theorem cm31_qm31R_not_isSquare : ¬ IsSquare qm31R := by
  rintro ⟨z, hz⟩
  apply m31_five_not_isSquare
  refine ⟨QuadraticAlgebra.norm z, ?_⟩
  calc
    (5 : M31Exact) = QuadraticAlgebra.norm qm31R := cm31_norm_qm31R.symm
    _ = QuadraticAlgebra.norm (z * z) := congrArg QuadraticAlgebra.norm hz
    _ = QuadraticAlgebra.norm z * QuadraticAlgebra.norm z :=
      QuadraticAlgebra.norm.map_mul z z

instance qm31Rootless : Fact
    (∀ z : CM31Exact, z ^ 2 ≠ qm31R + 0 * z) := ⟨by
  intro z hz
  apply cm31_qm31R_not_isSquare
  refine ⟨z, ?_⟩
  simpa [pow_two] using hz.symm
⟩

/-- Exact deployed quartic extension: `u^2 = 2+i`. -/
abbrev QM31Exact := QuadraticAlgebra CM31Exact qm31R 0

#print axioms cm31_qm31R_not_isSquare
end AspisV8R15.ExactTowerBase
