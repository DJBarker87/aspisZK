import NIT_AllocatorChain
import NIT_GuardComposition
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIT_PairComposition
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_PairControl

/-- Initial's all-cell observation determines the exact array passed to the
regular call, without a presumed successful pair result. -/
theorem initial_frame (alpha : Array E 2#usize) (l : Initial)
 (ap0 ap1 : Powers) (parts : Parts) (cut : cutInitial alpha l ap0 ap1 parts) :
 parts=initial := by
 apply NIT_ArrayFrames.ext NHI_Scalar.zero
 intro i hi
 have frame := cut.2.2.2.2.2.2 i hi
 change epick parts i=epick initial i
 rw [frame]
 change NHI_Scalar.zero=((List.replicate 7 NHI_Scalar.zero)[i]?).getD NHI_Scalar.zero
 rw [List.getElem?_replicate]
 simp only [hi,ite_true,Option.getD_some]

/-- Composition of the exact emitted control flow with the finite native-step
chains. This is a model-chain certificate; the native root joins are separately
identified in the open-edge report and are not silently made hypotheses here. -/
theorem full_model_chain (r : NP6_StdModel.Reservation) (c : Context)
 (domain : NIT_PairDomain.Domain c.w.value c.alpha.value c.f.value c.kappa)
 (powers0 : FIo_Native.weights.powers 4#usize (epick c.alpha.value 0)=ok c.ap0.value)
 (powers1 : FIo_Native.weights.powers 4#usize (epick c.alpha.value 1)=ok c.ap1.value)
 (c0 : canonical c.ap0.value) (c1 : canonical c.ap1.value) :
 ∃ out,NIT_AllocatorChain.Trace c r out ∧
 (letI:=FIo_Install.allocation r
  FIo_Native.weights.Weights.pair c.w.value c.alpha.value.to_slice c.f.value c.kappa=out) := by
 obtain ⟨out,trace,run⟩ := NIT_AllocatorChain.complete r c domain c0 c1
 refine ⟨out,trace,?_⟩
 letI:=FIo_Install.allocation r
 rw [NIT_PairDomain.source _ _ _ (NIT_PairDomain.message_size _ _ _ _ domain),
  NIT_PairControl.source c powers0 powers1]
 exact run

/-- Initial cut and CLOSED powers4 laws constructed together on the SAME actual
alphas. Addresses identify places only; no two Ref payloads are equated. -/
theorem initial_exists (alpha : Array E 2#usize) (canonical : canonical alpha) :
 ∃ (ap0 ap1 : Powers) (l : Initial),cutInitial alpha l ap0 ap1 initial ∧
 FIo_Native.weights.powers 4#usize (epick alpha 0)=ok ap0 ∧
 FIo_Native.weights.powers 4#usize (epick alpha 1)=ok ap1 ∧
 NIT_Cuts.canonical ap0 ∧ NIT_Cuts.canonical ap1 := by
 obtain ⟨ap0,ap1,l,parts,cut,p0,p1,c0,c1⟩ := NIT_PowersInstantiation.initial alpha canonical
 have same := initial_frame alpha l ap0 ap1 parts cut
 subst parts
 exact ⟨ap0,ap1,l,cut,p0,p1,c0,c1⟩

#print axioms initial_frame
#print axioms full_model_chain
#print axioms initial_exists
end AspisR1.NIT_PairComposition
