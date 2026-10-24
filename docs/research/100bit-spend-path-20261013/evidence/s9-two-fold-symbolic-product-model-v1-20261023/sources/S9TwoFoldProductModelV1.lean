import RoundPairing
set_option autoImplicit false
noncomputable section
namespace AspisR1S9TwoFoldProductModelV1
open AspisR1
variable {K : Type} [Field K]

def factor (alpha : K) (a : Fin 4 → K) : K :=
  (((((0 : K)+alpha^0*a 0)+alpha^3*a 1)+alpha^2*a 2)+alpha^1*a 3)*
    RoundPairing.quarter

/-- Reuse the existing dual-fold Horner theorem on four symbolic children;
no expansion of a 1024-coordinate source vector. -/
theorem dual_fold_child_product {n : Nat} (alpha : K) (w : Fin (4*n) → K)
    (d : Fin n) (a : Fin 4 → K) (b : K)
    (h : ∀ t, w (childIndex d t)=a t*b) :
    RoundPairing.dualFold alpha w d=factor alpha a*b := by
  rw [RoundPairing.dualFold_horner]
  unfold RoundPairing.dualHorner factor
  rw [h 0,h 3,h 2,h 1]
  ring

/-- The two actual radix-four child layers of a tensor row have the product
of the two source-ordered factor polynomials. This is model algebra only;
its child equalities must be supplied by the SAME constructor table/row. -/
theorem two_dual_fold_child_product {n : Nat}
    (alpha0 alpha1 : K) (w : Fin (4*(4*n)) → K)
    (a b : Fin 4 → K) (c : Fin n → K) (d : Fin n)
    (h : ∀ t1 t0, w (childIndex (childIndex d t1) t0)=a t0*b t1*c d) :
    RoundPairing.dualFold alpha1 (RoundPairing.dualFold alpha0 w) d=
      (factor alpha0 a*factor alpha1 b)*c d := by
  have hi : ∀ t1, RoundPairing.dualFold alpha0 w (childIndex d t1)=
      b t1*(factor alpha0 a*c d) := by
    intro t1
    have hh : ∀ t0, w (childIndex (childIndex d t1) t0)=a t0*(b t1*c d) := by
      intro t0
      rw [h t1 t0]
      ring
    rw [dual_fold_child_product alpha0 w (childIndex d t1) a (b t1*c d) hh]
    ring
  rw [dual_fold_child_product alpha1 (RoundPairing.dualFold alpha0 w) d b
    (factor alpha0 a*c d) hi]
  ring

#print axioms dual_fold_child_product
#print axioms two_dual_fold_child_product
end AspisR1S9TwoFoldProductModelV1
end
