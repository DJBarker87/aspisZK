import NEV_DotCarrier
set_option autoImplicit false
namespace AspisR1.NFC_CheckedArithmetic
open Aeneas Aeneas.Std Result

theorem add (a b c : Usize) (bound : a.val+b.val≤UScalar.max .Usize)
    (run : a+b=ok c) : c.val=a.val+b.val := by
  obtain ⟨actual,call,value⟩:=WP.spec_imp_exists (UScalar.add_spec (x:=a) (y:=b) bound)
  have same : actual=c := Result.ok.inj (call.symm.trans run)
  exact same ▸ value

theorem mul (a b c : Usize) (bound : a.val*b.val≤UScalar.max .Usize)
    (run : a*b=ok c) : c.val=a.val*b.val := by
  obtain ⟨actual,call,value⟩:=WP.spec_imp_exists (UScalar.mul_spec (x:=a) (y:=b) bound)
  have same : actual=c := Result.ok.inj (call.symm.trans run)
  exact same ▸ value
#print axioms add
#print axioms mul
end AspisR1.NFC_CheckedArithmetic
