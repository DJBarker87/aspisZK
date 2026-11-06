import NIT_SharedChain
import NJU_WeakPairDomain
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJU_WeakSharedChain
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_PairControl
open NIT_SharedChain
variable [FIo_Native.Allocation]

/- Generalized domain only. Original data/trace/evaluator definitions reused. -/
theorem shared_interpreted (c : Context) (parts : Parts) (out : Result NR)
 (domain : NJU_WeakPairDomain.Domain c.w.value c.alpha.value c.f.value c.kappa)
 (trace : Shared c parts out) : shared c parts=out := by
 cases trace with
 | failed owner cells e common call =>
  simp only [uncurry,shared,common_interpreted c domain.factors owner cells common,call,bind_tc_ok];rfl
 | diverged owner cells common call =>
  simp only [uncurry,shared,common_interpreted c domain.factors owner cells common,call,bind_tc_ok];rfl
 | returned owner cells reply out common call tail =>
  have hc := common_interpreted c domain.factors owner cells common
  have hs := hc
  rw [←NIG_CommonLoop.common_source] at hs
  have same := (NIG_PairFrames.common c.w.value domain.factors owner cells hs).1
  subst owner
  simp only [uncurry,shared,hc,call,bind_tc_ok]
  exact partial_interpreted c c.w parts reply out domain.s2 domain.size domain.extra tail


#print axioms shared_interpreted
end AspisR1.NJU_WeakSharedChain
