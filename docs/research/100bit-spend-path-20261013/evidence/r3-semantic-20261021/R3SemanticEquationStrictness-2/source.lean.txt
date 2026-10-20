import R3SemanticEquationCore

/-! Dropping the degree guard strictly weakens the arithmetic predicate on
arbitrary polynomials. Parser image membership restores that guard. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.R3SemanticEquationStrictness
open R3SemanticEquationCore Polynomial

/-- Boundary/terminal comparisons alone permit degree 28. This is a symbolic
counterexample, not a claim about any literal parser output or frozen source. -/
theorem equations_do_not_imply_degrees :
    ∃ polys : Fin 10 → Polynomial ℚ,
      Equations 1 0 (fun _ => 0) polys ∧
      ¬ (∀ j : Fin 10, (polys j).natDegree ≤ 27) := by
  classical
  let polys : Fin 10 → Polynomial ℚ := fun j => if j = 0 then X ^ 28 else 0
  refine ⟨polys, ?_, ?_⟩
  · constructor
    · simp [polys]
    constructor
    · intro j
      have hsucc : j.succ ≠ 0 := Fin.succ_ne_zero j
      simp only [polys, if_neg hsucc, eval_zero, zero_add]
      split_ifs <;> simp
    · simp [polys]
  · intro h
    have hd := h 0
    simp [polys] at hd

/-- Even perfect degree bounds do not enforce the initial field equation.
This obstruction holds over every field; no concrete coefficient reduction
or source acceptance interpretation is involved. -/
theorem degrees_do_not_imply_equations {K : Type} [Field K]
    (alpha : Fin 10 → K) :
    (∀ j : Fin 10, ((fun _ => (0 : Polynomial K)) j).natDegree ≤ 27) ∧
    ¬ Equations (1 : K) 0 alpha (fun _ => 0) := by
  constructor
  · intro j
    simp only [natDegree_zero]
    omega
  · intro h
    have hbad : (0 : K) = 1 := by
      simpa only [eval_zero, zero_add] using h.1
    exact zero_ne_one hbad

#print axioms equations_do_not_imply_degrees
#print axioms degrees_do_not_imply_equations
end AspisR1.R3SemanticEquationStrictness
end
