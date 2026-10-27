import R1Z.PV_Inv_Compression
import Mathlib.Algebra.BigOperators.Fin
set_option autoImplicit false
namespace R1Z.PV_Inv_CompressionFinite
open scoped BigOperators
open PV_Inv_Compression
variable {K : Type} [CommRing K]

theorem weighted_ofFn (n : ℕ) (lambda power : K) (f : Fin n → K) :
    weighted lambda power (List.ofFn f)=∑ i : Fin n, power*lambda^i.val*f i := by
  induction n generalizing power with
  | zero => simp [weighted]
  | succ n ih =>
    rw [List.ofFn_succ,weighted,ih,Fin.sum_univ_succ]
    simp only [Fin.val_zero,pow_zero,mul_one]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Fin.val_succ,pow_succ]
    ring

theorem tagged_sixteen (lambda tag : K) (f : Fin 16 → K) :
    loop lambda tag lambda (List.ofFn f)=tag+∑ i : Fin 16, lambda^(i.val+1)*f i := by
  rw [loop_eq,weighted_ofFn]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [pow_succ]
  ring

#print axioms weighted_ofFn
#print axioms tagged_sixteen
end R1Z.PV_Inv_CompressionFinite
