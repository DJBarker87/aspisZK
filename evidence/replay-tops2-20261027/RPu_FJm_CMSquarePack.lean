import RPu_FJm_SquareAlgebra
set_option autoImplicit false
namespace AspisR1.FJm_CMSquarePack

theorem tower {K : Type} [Field K] (r : K)
    [Fact (∀ x : K,x^2≠r+(0:K)*x)] (a b : K) :
    (⟨a*a+r*b*b,a*b+b*a⟩ : QuadraticAlgebra K r 0)=
      (⟨a,b⟩ : QuadraticAlgebra K r 0)*(⟨a,b⟩ : QuadraticAlgebra K r 0) := by
  apply QuadraticAlgebra.ext
  · simp only [QuadraticAlgebra.re_mul]
  · simp only [QuadraticAlgebra.im_mul]
    ring
#print axioms tower
end AspisR1.FJm_CMSquarePack
