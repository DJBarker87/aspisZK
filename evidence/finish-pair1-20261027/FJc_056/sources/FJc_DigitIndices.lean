import FJc_FieldOffsets
set_option autoImplicit false
namespace AspisR1.FJc_DigitIndices
open Aeneas Aeneas.Std Result WP

theorem rem4 (x r : Usize) (run : x%4#usize=ok r) : r.val=x.val%4 := by
  obtain ⟨r',hr,hv⟩ := WP.spec_imp_exists (UScalar.rem_spec x (y:=4#usize) (by decide))
  cases Result.ok.inj (hr.symm.trans run)
  simpa only [show (4#usize).val=4 from by scalar_tac] using hv

theorem div4 (x r : Usize) (run : x/4#usize=ok r) : r.val=x.val/4 := by
  obtain ⟨r',hr,hv⟩ := UScalar.div_spec x (y:=4#usize) (by decide)
  cases Result.ok.inj (hr.symm.trans run)
  simpa only [show (4#usize).val=4 from by scalar_tac] using hv
#print axioms rem4
#print axioms div4
end AspisR1.FJc_DigitIndices
