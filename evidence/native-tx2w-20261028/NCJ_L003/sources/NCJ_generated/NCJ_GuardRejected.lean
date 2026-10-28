import FIo_NativeFuns
set_option autoImplicit false
noncomputable section
namespace NCJ_GuardRejected
open Aeneas Aeneas.Std Result FIo_Native

theorem wrong_folds (w : weights.Weights) (folds : Usize)
    (h : folds ≠ 2#usize) : weights.shared_two_point_guard w folds = ok false := by
  cases hv : w.variant <;>
    simp [weights.shared_two_point_guard,
      transport.Variant.Insts.CoreCmpPartialEqVariant.eq, hv, h]

theorem s1 (w : weights.Weights) (h : w.variant = .S1) (folds : Usize) :
    weights.shared_two_point_guard w folds = ok false := by
  simp [weights.shared_two_point_guard,transport.Variant.Insts.CoreCmpPartialEqVariant.eq,transport.Variant.read_discriminant,h]

theorem d (w : weights.Weights) (h : w.variant = .D) (folds : Usize) :
    weights.shared_two_point_guard w folds = ok false := by
  simp [weights.shared_two_point_guard,transport.Variant.Insts.CoreCmpPartialEqVariant.eq,transport.Variant.read_discriminant,h]

#print axioms wrong_folds
#print axioms s1
#print axioms d
end NCJ_GuardRejected
