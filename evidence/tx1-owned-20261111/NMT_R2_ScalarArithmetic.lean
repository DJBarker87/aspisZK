import NMT_R2_WpResult
set_option autoImplicit false
namespace NMT_R2_ScalarArithmetic
open Aeneas Aeneas.Std

theorem mul (a b c : Usize) (value : a.val * b.val = c.val) :
 (a * b : Result Usize) = .ok c := by
 have safe : a.val * b.val ≤ Usize.max := by rw [value]; scalar_tac
 obtain ⟨z,hz,hv⟩ := NMT_R2_WpResult.source _ _ (Usize.mul_spec (x := a) (y := b) safe)
 have he : z = c := UScalar.eq_of_val_eq (hv.trans value)
 exact hz.trans (congrArg Result.ok he)

theorem sub (a b c : Usize) (inside : b.val ≤ a.val) (value : a.val - b.val = c.val) :
 (a - b : Result Usize) = .ok c := by
 obtain ⟨z,hz,hv⟩ := NMT_R2_WpResult.source _ _ (Usize.sub_spec (x := a) (y := b) inside)
 have he : z = c := UScalar.eq_of_val_eq (hv.1.trans value)
 exact hz.trans (congrArg Result.ok he)
#print axioms mul
#print axioms sub
end NMT_R2_ScalarArithmetic
