import RPu_FIw_WordValue
set_option autoImplicit false
namespace AspisR1.FIx_WordArithmetic
open Aeneas Aeneas.Std Result

theorem sub (x y out : Usize) (hy : y.val≤x.val) (run : x-y=ok out) :
    out.val=x.val-y.val := by
  obtain ⟨z,hz,hv⟩ := WP.spec_imp_exists (UScalar.sub_spec (x := x) (y := y) hy)
  have same := Result.ok.inj (run.symm.trans hz)
  subst z
  exact hv.1

theorem div (x y out : Usize) (hy : y.val≠0) (run : x/y=ok out) :
    out.val=x.val/y.val := by
  obtain ⟨z,hz,hv⟩ := UScalar.div_spec (x := x) (y := y) hy
  have same := Result.ok.inj (run.symm.trans hz)
  subst z
  exact hv
#print axioms sub
#print axioms div
end AspisR1.FIx_WordArithmetic
