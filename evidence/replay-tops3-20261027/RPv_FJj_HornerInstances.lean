import RPv_FJg_QuarterHorner
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJj_HornerInstances

def horner {R : Type} [CommRing R] (f : Fin 4 → R) (a : R) : R :=
  f 0+a*(f 3+a*(f 2+a*f 1))

/-- Compare the two instance paths before specializing any tower constants. -/
theorem tower {K : Type} [Field K] (r u : K)
    [Fact (∀ x : K,x^2≠r+u*x)] (f : Fin 4 → QuadraticAlgebra K r u)
    (a : QuadraticAlgebra K r u) :
    horner f a=FJg_LowHorner.horner f a := rfl

#print axioms tower
end AspisR1.FJj_HornerInstances
end
