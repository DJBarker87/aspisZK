import NNX_Masked
import JFu_CircleAlgebra
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNX_Comparisons
open Aeneas Aeneas.Std Result AspisR1PublicPreparation

theorem qm_ne (x : aspis_core.field.QM31) :
 core.cmp.PartialEq.ne.trait_default aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 x x = .ok false := by
 simp only [core.cmp.PartialEq.ne.trait_default,core.cmp.PartialEq.ne.default,
  aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31,FIr_FinishComparison.qm_eq_source,
  decide_true,bind_tc_ok,Bool.not_true]

theorem point (x y : aspis_core.circle.SecureCirclePoint) (different : x ≠ y) :
 FinishModel.pointEq x y = .ok false :=
 JFu_CircleAlgebra.comparison x y different

#print axioms qm_ne
#print axioms point
end AspisR1.NNX_Comparisons
end
