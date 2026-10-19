import ActualMainMaskPopulatedBridge

/-! The finish comparison's concrete source arithmetic implies the exact
field equation used by the masked sumcheck relation. All inputs refer to the
same successful call chain; canonicality is retained where not yet derived
from the caller. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1PublicPreparation.ActualFinishFieldEquation
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.RawSemanticFieldOwnerAdapter
open AspisR1PublicPreparation.ActualFinishConcreteArithmeticBoundary
open AspisR1PublicPreparation.ActualMainMaskPopulatedBridge

 theorem add_success_exact (x y out : MainQM)
    (hx : Canonical (mainToProbe x)) (hy : Canonical (mainToProbe y))
    (h : extractedMainAdd x y = .ok out) :
    Canonical (mainToProbe out) ∧ fieldValue out = fieldValue x + fieldValue y := by
  obtain ⟨z,hz,hzc,hzv⟩ := extractedMainAdd_refines x y hx hy
  have heq : z = out := by injection (hz.symm.trans h)
  subst out
  refine ⟨hzc, ?_⟩
  exact hzv

 theorem mul_success_exact (x y out : MainQM)
    (hx : Canonical (mainToProbe x)) (hy : Canonical (mainToProbe y))
    (h : extractedMainMul x y = .ok out) :
    Canonical (mainToProbe out) ∧ fieldValue out = fieldValue x * fieldValue y := by
  obtain ⟨z,hz,hzc,hzv⟩ := extractedMainMul_refines x y hx hy
  have heq : z = out := by injection (hz.symm.trans h)
  subst out
  refine ⟨hzc, ?_⟩
  exact hzv

/-- No desired mask or arithmetic equation is assumed. The exact masked
terminal equation follows from the reached concrete mask/mul/add calls. -/
theorem terminal_chain_equation
    (c1 : Array MainQM 16#usize) (maskOnly : Array MainQM 10#usize)
    (g : MainQM) (point : Array MainQM 10#usize)
    (eta terminal extra running mask etaTerminal masked : MainQM)
    (hc1 : CanonicalArray c1) (hmaskOnly : CanonicalArray maskOnly)
    (hg : Canonical (mainToProbe g)) (hpoint : CanonicalArray point)
    (heta : Canonical (mainToProbe eta))
    (hterminal : Canonical (mainToProbe terminal))
    (hextra : Canonical (mainToProbe extra))
    (hm : extractedMainMask c1 maskOnly g point = .ok mask)
    (het : extractedMainMul eta terminal = .ok etaTerminal)
    (hadd : extractedMainAdd mask etaTerminal = .ok masked)
    (hfinal : extractedMainAdd masked extra = .ok running) :
    Canonical (mainToProbe running) ∧
      fieldValue running = maskValue c1 maskOnly g point +
        fieldValue eta * fieldValue terminal + fieldValue extra := by
  obtain ⟨mask',hm',hmc,hmv⟩ :=
    extractedMainMask_refines c1 maskOnly g point hc1 hmaskOnly hg hpoint
  have heq : mask' = mask := by injection (hm'.symm.trans hm)
  subst mask'
  obtain ⟨hetc,hetv⟩ := mul_success_exact eta terminal etaTerminal heta hterminal het
  obtain ⟨hmaskedc,hmaskedv⟩ := add_success_exact mask etaTerminal masked hmc hetc hadd
  obtain ⟨hrunningc,hrunningv⟩ := add_success_exact masked extra running hmaskedc hextra hfinal
  exact ⟨hrunningc, by rw [hrunningv,hmaskedv,hmv,hetv]⟩

#print axioms add_success_exact
#print axioms mul_success_exact
#print axioms terminal_chain_equation
end AspisR1PublicPreparation.ActualFinishFieldEquation
end
