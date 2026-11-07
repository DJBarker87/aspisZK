import NMT_R2_Base
set_option autoImplicit false
namespace NMT_R2_AllocIfLaws
open RSL

theorem lift_pure {A : Type} (a : A) : RS.lift (Spec.pure a) = RS.pure a := by
 unfold RS.lift Spec.map
 rw [Spec.bind_pure]
 rfl

theorem skipped {A : Type} (suffix : RS A) : RS.seq (RS.lift (Spec.allocIf false)) suffix = suffix := by
 change RS.seq (RS.lift (Spec.pure ())) suffix = suffix
 rw [lift_pure,RS.seq_pure]
#print axioms lift_pure
#print axioms skipped
end NMT_R2_AllocIfLaws
