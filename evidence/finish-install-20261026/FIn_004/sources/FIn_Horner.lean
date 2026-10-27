import R1OpeningPolynomialView
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIn_Horner
open scoped BigOperators

theorem seven {K : Type} [CommRing K] (f : Fin 7 → K) (x : K) :
    ((((((0*x+f 6)*x+f 5)*x+f 4)*x+f 3)*x+f 2)*x+f 1)*x+f 0 =
      ∑ i : Fin 7, f i*x^i.val := by
  simp only [Fin.sum_univ_succ,Fin.val_zero,Fin.val_succ,Finset.univ_eq_empty,
    Finset.sum_empty,add_zero]
  change _ = f 0*x^0 + (f 1*x^1 + (f 2*x^2 + (f 3*x^3 + (f 4*x^4 + (f 5*x^5 + f 6*x^6)))))
  ring

#print axioms seven
end AspisR1.FIn_Horner
end
