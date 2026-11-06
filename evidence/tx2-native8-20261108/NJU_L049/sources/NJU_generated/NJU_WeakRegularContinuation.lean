import NJF_RegularContinuation
import NJU_WeakPairDomain
import NJU_WeakAlignRegularPhaseSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJU_WeakRegularContinuation
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_PairControl AspisR1Stage2
open NJF_RegularCut NJF_RegularInstantiation NJF_SharedContinuation
open NJF_RegularContinuation
variable [FIo_Native.Allocation]

/- Generalized domain only. Original data/trace/evaluator definitions reused. -/
theorem source (c : Context) (before : Scratch)
 (domain : NJU_WeakPairDomain.Domain c.w.value c.alpha.value c.f.value c.kappa)
 (c0 : canonical c.ap0.value) (c1 : canonical c.ap1.value)
 (inv : NHX_RegularPost.Inv before initial) :
 continueWith c (G (NGM_GuardExact.guard c.w.value 2#usize) (instantiate c before)).1=
 (NIW_AlignRegularPhase.run c before).1 := by
 rw [NJF_RegularInstantiation.source]
 exact (interpreted c before domain.factors).trans (NJU_WeakAlignRegularPhaseSource.source c before domain c0 c1 inv)


#print axioms source
end AspisR1.NJU_WeakRegularContinuation
