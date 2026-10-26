import R1OpeningPolynomialView
import FIn_Primitives
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

theorem fold_seven {K : Type} [CommRing K] (f : Fin 7 → K) (g : Aeneas.Std.Usize → K) (x : K)
    (h0 : g 0#usize = f 0)
    (h1 : g 1#usize = f 1)
    (h2 : g 2#usize = f 2)
    (h3 : g 3#usize = f 3)
    (h4 : g 4#usize = f 4)
    (h5 : g 5#usize = f 5)
    (h6 : g 6#usize = f 6)
    : [6#usize,5#usize,4#usize,3#usize,2#usize,1#usize,0#usize].foldl
      (fun acc i => acc*x+g i) 0 = ∑ i : Fin 7, f i*x^i.val := by
  simp only [List.foldl_cons,List.foldl_nil]
  rw [h0,h1,h2,h3,h4,h5,h6]
  exact seven f x

#print axioms seven
#print axioms fold_seven
end AspisR1.FIn_Horner
end
