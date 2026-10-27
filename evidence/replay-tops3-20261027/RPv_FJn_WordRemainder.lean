import RPv_FIx_WordArithmetic
set_option autoImplicit false
namespace AspisR1.FJn_WordRemainder
open Aeneas Aeneas.Std Result WP
/-- Bounded word remainder keeps the natural index used by the gather. -/
theorem value (x r : Usize) (run : x%28#usize=ok r) : r.val=x.val%28 := by
  obtain ⟨r',hr,hv⟩:=WP.spec_imp_exists (UScalar.rem_spec x (y:=28#usize) (by decide))
  cases Result.ok.inj (hr.symm.trans run)
  exact hv
#print axioms value
end AspisR1.FJn_WordRemainder
