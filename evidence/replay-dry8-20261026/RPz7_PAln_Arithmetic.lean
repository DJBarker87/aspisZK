import RPz7_PSem_Control
set_option autoImplicit false
namespace AspisR1.PAln_Arithmetic
open Aeneas Aeneas.Std Result

theorem add (a b c : Usize) (same : c.val=a.val+b.val) : a+b=ok c := by
  obtain ⟨r,call,value⟩ := WP.spec_imp_exists (UScalar.add_spec (x:=a) (y:=b) (by scalar_tac))
  have equal : r=c := by scalar_tac
  simpa only [equal] using call

theorem mul (a b c : Usize) (same : c.val=a.val*b.val) : a*b=ok c := by
  obtain ⟨r,call,value⟩ := WP.spec_imp_exists (UScalar.mul_spec (x:=a) (y:=b) (by scalar_tac))
  have equal : r=c := by scalar_tac
  simpa only [equal] using call

theorem sub (a b c : Usize) (bound : b.val≤a.val) (same : c.val=a.val-b.val) : a-b=ok c := by
  obtain ⟨r,call,value⟩ := WP.spec_imp_exists (UScalar.sub_spec (x:=a) (y:=b) (by scalar_tac))
  have equal : r=c := by scalar_tac
  simpa only [equal] using call

#print axioms add
#print axioms mul
#print axioms sub
end AspisR1.PAln_Arithmetic
