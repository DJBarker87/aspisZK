import AspisV8R19.R670AllPointResidualRepair
import AspisV8R19.R665FullSourceP2Boundary
import Mathlib.Tactic
set_option autoImplicit false
namespace AspisV8R19.R675FullCorrectionMoments
open AspisR19 AspisV8R17 HighRepairInvariant BetaUniformCorrection
open R660FullSourceResidualCorrection R665FullSourceP2Boundary
open scoped BigOperators
noncomputable section
variable {F : Type*} [Field F] [NeZero (2 : F)]

theorem full_extension_moment_zero (half quarter a b c kappa tau : F)
    (z : Fin 10 → F) (previous : Fin 271 → F) (structured : Bool)
    (q : Index 32 → F) (hquarter : quarter ≠ 0)
    (h : TwoSwapResidualSource.relation half quarter a b c kappa tau z previous structured q 0 +
      TwoSwapResidualSource.relation half quarter a b c kappa tau z previous structured q 4 = 0) :
    (∑ d : Fin 256, ∑ s : Fin 4, extendCorrection q (d,s) *
      fullWeight half a b c kappa tau z previous structured (d,s)) = 0 := by
  have hb := R653SourceCoefficientBoundary.coefficient_boundary 256 quarter
    (extendCorrection q) (fullWeight half a b c kappa tau z previous structured)
  change fullRelation half quarter a b c kappa tau z previous structured (extendCorrection q) 0 +
    fullRelation half quarter a b c kappa tau z previous structured (extendCorrection q) 4 = _ at hb
  rw [full_extension_relation, full_extension_relation] at hb
  rw [h, zero_add] at hb
  exact (mul_eq_zero.mp hb.symm).resolve_left hquarter

theorem full_moment_add (q r : Index 256 → F) (w : Index 256 → F) :
    (∑ d : Fin 256, ∑ s : Fin 4, (q (d,s)+r (d,s))*w (d,s)) =
      (∑ d : Fin 256, ∑ s : Fin 4, q (d,s)*w (d,s)) +
      (∑ d : Fin 256, ∑ s : Fin 4, r (d,s)*w (d,s)) := by
  rw [Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  ring

theorem p2_of_moments (half a b c kappa tau scale : F)
    (z : Fin 10 → F) (previous : Fin 271 → F) (r g : Index 256 → F)
    (hr : (∑ d : Fin 256, ∑ s : Fin 4, r (d,s)*fullWeight half a b c kappa tau z previous false (d,s))=0)
    (hg : (∑ d : Fin 256, ∑ s : Fin 4, g (d,s)*fullWeight half a b c kappa tau z previous true (d,s))=0)
    (hc : (∑ d : Fin 256, ∑ s : Fin 4, r (d,s)*fullWeight half a b c kappa tau z previous true (d,s)) + scale*
      (∑ d : Fin 256, ∑ s : Fin 4, g (d,s)*fullWeight half a b c kappa tau z previous false (d,s))=0) :
    scale * (rangeDot 1024 (TwoSwapResidualSource.quotientWeight half a b c kappa tau z previous true) (flattenFull g) -
      rangeDot 1024 (TwoSwapResidualSource.quotientWeight half a b c kappa tau z previous false) (flattenFull g)) -
      (rangeDot 1024 (TwoSwapResidualSource.quotientWeight half a b c kappa tau z previous true) (flattenFull r) -
      rangeDot 1024 (TwoSwapResidualSource.quotientWeight half a b c kappa tau z previous false) (flattenFull r))=0 := by
  simp only [full_flatten_pairing]
  exact p2_retained _ _ _ _ scale hr hc hg

#print axioms full_extension_moment_zero
#print axioms full_moment_add
#print axioms p2_of_moments
end
end AspisV8R19.R675FullCorrectionMoments
