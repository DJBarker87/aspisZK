import AspisV8R19.R370KernelEvaluation

/-! An independent audit of the literal R370 constants cited by the paper.
Keep separate from Wide imports, which conflict with the V8 natural-basis
namespace. These historical counterexamples refute only the former unscaled
form, corrected by owner decision in cd5eb4226. -/
set_option autoImplicit false
namespace AspisR0.CitedKernelAudit
open AspisR19.R370KernelEvaluation
open scoped BigOperators
variable {F : Type*} [Field F]

def impulse : Fin 256 × Fin 4 → F :=
  fun i => if i.1 = 0 ∧ i.2 = 0 then 1 else 0

/-- On the same first-coordinate witness, the literal imported R370 kernel
has value `quarter` and its unscaled fold pairing has value one. -/
theorem literal_cited_kernel (quarter alpha : F) :
    kernelEval 256 quarter alpha impulse impulse = quarter ∧
    (∑ d : Fin 256, firstFold 256 alpha impulse d * dualFold 256 alpha impulse d) = 1 := by
  have primal (d : Fin 256) : firstFold 256 alpha (impulse (F := F)) d =
      if d = 0 then 1 else 0 := by
    by_cases hd : d = 0 <;> simp [firstFold, impulse, hd]
  have dual (d : Fin 256) : dualFold 256 alpha (impulse (F := F)) d =
      if d = 0 then 1 else 0 := by
    by_cases hd : d = 0 <;> simp [dualFold, impulse, hd]
  have pairing : (∑ d : Fin 256,
      firstFold 256 alpha (impulse (F := F)) d * dualFold 256 alpha impulse d) = 1 := by
    simp only [primal, dual]
    simp
  exact ⟨by rw [kernel_eval_pairing, pairing, mul_one], pairing⟩

theorem literal_cited_counterexample (quarter alpha : F) (h : quarter ≠ 1) :
    kernelEval 256 quarter alpha impulse impulse ≠
      ∑ d : Fin 256, firstFold 256 alpha impulse d * dualFold 256 alpha impulse d := by
  rw [(literal_cited_kernel quarter alpha).1, (literal_cited_kernel quarter alpha).2]
  exact h

#print axioms literal_cited_kernel
#print axioms literal_cited_counterexample
end AspisR0.CitedKernelAudit
