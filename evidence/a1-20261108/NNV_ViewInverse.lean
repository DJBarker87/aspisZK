import NNV_PreparedInputs
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNV_ViewInverse
open Aeneas Aeneas.Std Result AspisR1CurrentCaller

theorem field (e : aspis_core.field.wide_exact.WideExact) :
 InstalledPreparation.currentE (InstalledPreparation.retainedE e) = e := by cases e; rfl

theorem source (v : verifier.View) : NNV_PreparedInputs.view (InstalledPreparation.retainedView v) = v := by
 cases v with
 | mk variant semantic y1 inactive round0 root round1 final_ query =>
  cases variant <;> rfl
#print axioms field
#print axioms source
end AspisR1.NNV_ViewInverse
end
