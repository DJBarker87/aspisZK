import Aeneas
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCI_SizeArithmetic

def sum (a b : Usize) (bound : a.val+b.val<65536) : Usize :=
  Usize.ofNat (a.val+b.val) (by scalar_tac)

theorem add (a b : Usize) (bound : a.val+b.val<65536) :
    a+b=ok (sum a b bound) := by
  obtain ⟨z,hz,hvalue⟩ := WP.spec_imp_exists
    (UScalar.add_spec (x:=a) (y:=b) (by scalar_tac))
  have he : z=sum a b bound := by
    apply UScalar.eq_of_val_eq
    exact hvalue
  simpa only [he] using hz

theorem checked (a b : Usize) (bound : a.val+b.val<65536) :
    Usize.checked_add a b=some (sum a b bound) := by
  simp only [Usize.checked_add,core.num.checked_add_UScalar,add a b bound,Option.ofResult]

#print axioms add
#print axioms checked
end PCI_SizeArithmetic
