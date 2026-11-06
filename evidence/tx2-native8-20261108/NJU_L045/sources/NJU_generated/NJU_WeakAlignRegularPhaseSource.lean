import NIW_AlignRegularPhaseSource
import NJU_WeakPairDomain
import NJU_WeakRegularChain
import NJU_WeakAlignRegularPhase
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJU_WeakAlignRegularPhaseSource
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_PairControl
open NIW_AlignRegularPhaseSource
variable [FIo_Native.Allocation]

/- Generalized domain only. Original data/trace/evaluator definitions reused. -/
theorem source (c : Context) (before : Scratch)
 (domain : NJU_WeakPairDomain.Domain c.w.value c.alpha.value c.f.value c.kappa)
 (c0 : canonical c.ap0.value) (c1 : canonical c.ap1.value)
 (inv : NHX_RegularPost.Inv before initial) :
 NIT_PairControl.regular c before=(NIW_AlignRegularPhase.run c before).1 :=
 NJU_WeakRegularChain.interpreted c before _ domain (NJU_WeakAlignRegularPhase.trace c before domain c0 c1 inv)


theorem frames (c : Context) (before : Scratch)
 (domain : NJU_WeakPairDomain.Domain c.w.value c.alpha.value c.f.value c.kappa)
 (c0 : canonical c.ap0.value) (c1 : canonical c.ap1.value)
 (inv : NHX_RegularPost.Inv before initial) :
 ∀ event∈(NIW_AlignRegularPhase.run c before).2.events,NIW_AlignRegularFrames.Frame event := by
 rw [events]
 exact NIW_AlignRegularFrames.all c.w.value c.alpha.value.to_slice c.f.value c.ap0.value c.ap1.value
  domain.s2 domain.factors c0 c1 _
  (fun k hk=>NHM_RegularDomain.membership (NGM_GuardExact.guard c.w.value 2#usize) k hk) before initial inv


#print axioms source
#print axioms frames
end AspisR1.NJU_WeakAlignRegularPhaseSource
