import NDO_JFr_BoundaryTrace
set_option autoImplicit false
namespace AspisR1.JFr_IndexArithmetic
open Aeneas Aeneas.Std Result WP

theorem add (i j : Usize) (value : i.val+1=j.val) : i+1#usize=ok j := by
  have spec : (i+1#usize : Result Usize) ⦃ out => out.val=i.val+1 ⦄ := by
    step* <;> scalar_tac
  obtain ⟨out,call,num⟩ := WP.spec_imp_exists spec
  have same : out=j := UScalar.eq_of_val_eq (num.trans value)
  exact same ▸ call

theorem sub (i j : Usize) (value : j.val+1=i.val) : i-1#usize=ok j := by
  have spec : (i-1#usize : Result Usize) ⦃ out => out.val=i.val-1 ⦄ := by
    step* <;> scalar_tac
  obtain ⟨out,call,num⟩ := WP.spec_imp_exists spec
  have same : out=j := UScalar.eq_of_val_eq (by omega)
  exact same ▸ call

#print axioms add
#print axioms sub
end AspisR1.JFr_IndexArithmetic
