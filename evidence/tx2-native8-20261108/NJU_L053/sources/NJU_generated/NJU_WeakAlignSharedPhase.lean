import NIW_AlignSharedPhase
import NJU_WeakPairDomain
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJU_WeakAlignSharedPhase
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_PairControl
open NIW_AlignSharedPhase
variable [FIo_Native.Allocation]

/- Generalized domain only. Original data/trace/evaluator definitions reused. -/
theorem trace (c : Context) (parts : Parts)
 (domain : NJU_WeakPairDomain.Domain c.w.value c.alpha.value c.f.value c.kappa)
 (c0 : canonical c.ap0.value) (c1 : canonical c.ap1.value) (cp : canonical parts) :
 NIT_SharedChain.Shared c parts (run c parts).1 := by
 have cz : NHI_CellCanon.array (Array.repeat 16#usize NHX_FilledZero.zeroQ) := by
  intro x hx
  simp only [Array.repeat,List.mem_replicate] at hx
  exact hx.2 ▸ NHX_FilledZero.zero_canonical
 have observed := (NIW_AlignCommonSource.source c.w.value domain.factors _ cz).2
 cases result : (NIW_AlignCommonCollect.collect c.w.value 17
  ({start:=0#usize,«end»:=16#usize},Array.repeat 16#usize NHX_FilledZero.zeroQ)).1 with
 | fail err => simp only [result,NIW_AlignFieldReply.Produced] at observed
 | div => simp only [result,NIW_AlignFieldReply.Produced] at observed
 | ok value =>
  rcases value with ⟨owner,cells⟩
  simp only [result,NIW_AlignFieldReply.Produced] at observed
  have same := observed.2.1
  subst owner
  cases partialCall : FIo_Native.weights.shared_partials c.f.value cells with
  | fail err =>
   simp only [NIW_AlignSharedPhase.run,result,partialCall]
   exact .failed c.w.value cells err observed.1 partialCall
  | div =>
   simp only [NIW_AlignSharedPhase.run,result,partialCall]
   exact .diverged c.w.value cells observed.1 partialCall
  | ok reply =>
   simp only [NIW_AlignSharedPhase.run,result,partialCall]
   exact .returned c.w.value cells reply _ observed.1 partialCall
    (NIW_AlignPartialPhase.trace c c.w parts reply domain.s2
     domain.size domain.factors domain.extra c0 c1 cp domain.kappa)


#print axioms trace
end AspisR1.NJU_WeakAlignSharedPhase
