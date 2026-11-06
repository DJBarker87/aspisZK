import NIW_AlignRegularPhase
import NJU_WeakPairDomain
import NJU_WeakAlignAfterPhase
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJU_WeakAlignRegularPhase
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_PairControl
open NIW_AlignRegularPhase
variable [FIo_Native.Allocation]

/- Generalized domain only. Original data/trace/evaluator definitions reused. -/
theorem trace (c : Context) (before : Scratch)
 (domain : NJU_WeakPairDomain.Domain c.w.value c.alpha.value c.f.value c.kappa)
 (c0 : canonical c.ap0.value) (c1 : canonical c.ap1.value)
 (inv : NHX_RegularPost.Inv before initial) :
 NIT_RegularChain.Trace c before (run c before).1 := by
 have source := NIW_AlignRegularExecution.source c.w.value
  (NGM_GuardExact.guard c.w.value 2#usize) c.alpha.value.to_slice c.f.value c.ap0.value c.ap1.value before initial
 cases result : (NIW_AlignRegularExecution.execute c.w.value c.alpha.value.to_slice c.f.value
  c.ap0.value c.ap1.value (NHM_RegularKinds.kinds (NGM_GuardExact.guard c.w.value 2#usize)) before initial).1 with
 | fail err =>
  have call := source.trans result
  simp only [NIW_AlignRegularPhase.run,result]
  exact .failed err call
 | div =>
  have call := source.trans result
  simp only [NIW_AlignRegularPhase.run,result]
  exact .diverged call
 | ok value =>
  rcases value with ⟨reply,after,parts⟩
  have call := source.trans result
  have post := NIG_PairFrames.regular c.w.value _ c.alpha.value.to_slice c.f.value c.ap0.value c.ap1.value
   domain.s2 domain.factors c0 c1 before after initial parts reply inv call
  simp only [NIW_AlignRegularPhase.run,result]
  exact .returned reply after parts _ call
   (NJU_WeakAlignAfterPhase.trace c _ parts reply domain c0 c1 post.2.2)


#print axioms trace
end AspisR1.NJU_WeakAlignRegularPhase
