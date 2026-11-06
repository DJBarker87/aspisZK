import NIW_AlignPairPhase
import NJU_WeakPairDomain
import NJU_WeakAlignAllocatorPhase
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJU_WeakAlignPairPhase
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_PairControl
open NIW_AlignPairPhase

/- Generalized domain only. Original data/trace/evaluator definitions reused. -/
theorem certificate (r : NP6_StdModel.Reservation) (i : Input)
 (domain : NJU_WeakPairDomain.Domain i.owner.value i.alpha.value i.message.value i.kappa) :
 Certificate r i (run r i) := by
 have p0 := NIW_AlignPowersReply.source 4#usize (epick i.alpha.value 0)
  (NIT_PairComposition.epick_canonical i.alpha.value domain.alphas 0)
 have p1 := NIW_AlignPowersReply.source 4#usize (epick i.alpha.value 1)
  (NIT_PairComposition.epick_canonical i.alpha.value domain.alphas 1)
 cases call0 : FIo_Native.weights.powers 4#usize (epick i.alpha.value 0) with
 | fail err => simp only [call0,NIW_AlignFieldReply.Produced] at p0
 | div => simp only [call0,NIW_AlignFieldReply.Produced] at p0
 | ok ap0 =>
  simp only [call0,NIW_AlignFieldReply.Produced] at p0
  cases call1 : FIo_Native.weights.powers 4#usize (epick i.alpha.value 1) with
  | fail err => simp only [call1,NIW_AlignFieldReply.Produced] at p1
  | div => simp only [call1,NIW_AlignFieldReply.Produced] at p1
  | ok ap1 =>
   simp only [call1,NIW_AlignFieldReply.Produced] at p1
   simp only [NIW_AlignPairPhase.run,call0,call1,Certificate]
   exact ⟨True.intro,True.intro,p0,p1,NJU_WeakAlignAllocatorPhase.trace r (context i ap0 ap1) domain p0 p1⟩


#print axioms certificate
end AspisR1.NJU_WeakAlignPairPhase
