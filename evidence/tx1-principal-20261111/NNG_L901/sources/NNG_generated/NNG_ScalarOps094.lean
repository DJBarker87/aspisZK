import Aeneas
set_option autoImplicit false
namespace AspisR1.NNG_ScalarOps094
open Aeneas Aeneas.Std Result

theorem add (a b c : Usize) (value : a.val+b.val=c.val) : (a+b : Result Usize)=ok c := by
 have safe : a.val+b.val≤Usize.max := by rw [value];scalar_tac
 obtain ⟨v,run,val⟩ := WP.spec_imp_exists (Usize.add_spec (x:=a) (y:=b) safe)
 have same : v=c := UScalar.eq_of_val_eq (val.trans value)
 exact same ▸ run
#print axioms add

theorem mul (a b c : Usize) (value : a.val*b.val=c.val) : (a*b : Result Usize)=ok c := by
 have safe : a.val*b.val≤Usize.max := by rw [value];scalar_tac
 obtain ⟨v,run,val⟩ := WP.spec_imp_exists (Usize.mul_spec (x:=a) (y:=b) safe)
 have same : v=c := UScalar.eq_of_val_eq (val.trans value)
 exact same ▸ run
#print axioms mul

theorem sub (a b c : Usize) (safe : b.val≤a.val) (value : a.val-b.val=c.val) : (a-b : Result Usize)=ok c := by
 obtain ⟨v,run,val⟩ := WP.spec_imp_exists (Usize.sub_spec (x:=a) (y:=b) safe)
 have same : v=c := UScalar.eq_of_val_eq (val.1.trans value)
 exact same ▸ run
#print axioms sub
end AspisR1.NNG_ScalarOps094
