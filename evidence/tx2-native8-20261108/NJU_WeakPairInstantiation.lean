import NJF_PairInstantiation
import NJU_WeakPairDomain
import NJU_WeakAlignPairPhaseSource
import NJU_WeakAllocatorInstantiation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJU_WeakPairInstantiation
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_PairControl NIW_AlignPairPhase
open NJF_PairInstantiation

/- Generalized domain only. Original data/trace/evaluator definitions reused. -/
theorem source (r : NP6_StdModel.Reservation) (i : Input)
 (domain : NJU_WeakPairDomain.Domain i.owner.value i.alpha.value i.message.value i.kappa) :
 G r i=(NIW_AlignPairPhase.run r i).1 := by
 have p0 := NIW_AlignPowersReply.source 4#usize (epick i.alpha.value 0)
  (NIT_PairComposition.epick_canonical i.alpha.value domain.alphas 0)
 have p1 := NIW_AlignPowersReply.source 4#usize (epick i.alpha.value 1)
  (NIT_PairComposition.epick_canonical i.alpha.value domain.alphas 1)
 cases h0 : FIo_Native.weights.powers 4#usize (epick i.alpha.value 0) with
 | fail err => simp only [h0,NIW_AlignFieldReply.Produced] at p0
 | div => simp only [h0,NIW_AlignFieldReply.Produced] at p0
 | ok ap0 =>
  simp only [h0,NIW_AlignFieldReply.Produced] at p0
  cases h1 : FIo_Native.weights.powers 4#usize (epick i.alpha.value 1) with
  | fail err => simp only [h1,NIW_AlignFieldReply.Produced] at p1
  | div => simp only [h1,NIW_AlignFieldReply.Produced] at p1
  | ok ap1 =>
   simp only [h1,NIW_AlignFieldReply.Produced] at p1
   simp only [G,NIW_AlignPairPhase.run,h0,h1]
   exact NJU_WeakAllocatorInstantiation.source r (context i ap0 ap1) domain p0 p1

/-- Printed pair root: native G specializes to the emitted frozen pair body.
The Kani/cut transcriptions are the separately reviewed native half. -/

theorem root (r : NP6_StdModel.Reservation) (i : Input)
 (domain : NJU_WeakPairDomain.Domain i.owner.value i.alpha.value i.message.value i.kappa) :
 (letI:=FIo_Install.allocation r
  FIo_Native.weights.Weights.pair i.owner.value i.alpha.value.to_slice i.message.value i.kappa)=G r i ∧
 NIT_ResultCanonical.Canonical (G r i) := by
 rw [source r i domain]
 exact NJU_WeakAlignPairPhaseSource.source r i domain


#print axioms source
#print axioms root
end AspisR1.NJU_WeakPairInstantiation
