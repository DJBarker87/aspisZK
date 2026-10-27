import Aeneas
set_option autoImplicit false
namespace R1Z.ProverRwDictionaryLayoutArithmetic
open Aeneas Aeneas.Std Result

theorem add_eq (a b c : Usize) (h : a.val+b.val=c.val) :
    (a+b : Result Usize) = .ok c := by
  have bound : a.val+b.val ≤ Usize.max := by rw [h]; scalar_tac
  obtain ⟨z,hz,hv⟩ : ∃ z : Usize, (a+b : Result Usize)=.ok z ∧ z.val=a.val+b.val := by
    apply WP.spec_imp_exists
    apply UScalar.add_spec
    simpa only [UScalar.max_USize_eq] using bound
  have he : z=c := UScalar.eq_of_val_eq (by omega)
  simpa only [he] using hz

theorem mul_eq (a b c : Usize) (h : a.val*b.val=c.val) :
    (a*b : Result Usize) = .ok c := by
  have bound : a.val*b.val ≤ Usize.max := by rw [h]; scalar_tac
  obtain ⟨z,hz,hv⟩ : ∃ z : Usize, (a*b : Result Usize)=.ok z ∧ z.val=a.val*b.val := by
    apply WP.spec_imp_exists
    apply UScalar.mul_spec
    simpa only [UScalar.max_USize_eq] using bound
  have he : z=c := UScalar.eq_of_val_eq (by omega)
  simpa only [he] using hz

theorem sub_eq (a b c : Usize) (hle : b.val ≤ a.val) (h : a.val-b.val=c.val) :
    (a-b : Result Usize) = .ok c := by
  obtain ⟨z,hz,hv⟩ := WP.spec_imp_exists (UScalar.sub_spec (x:=a) (y:=b) hle)
  have he : z=c := UScalar.eq_of_val_eq (by omega)
  simpa only [he] using hz

#print axioms add_eq
#print axioms mul_eq
#print axioms sub_eq
end R1Z.ProverRwDictionaryLayoutArithmetic
