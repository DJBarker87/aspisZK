import NJF_AllocatorInstantiation
import NIW_AlignPairPhaseSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJF_PairInstantiation
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_PairControl NIW_AlignPairPhase

/-- Initial/powers and allocator/regular stages composed in frozen source order.
Logged replies are actual CLOSED child calls at the decoded arguments. -/
def G (r : NP6_StdModel.Reservation) (i : Input) : Result NR :=
 match FIo_Native.weights.powers 4#usize (epick i.alpha.value 0) with
 | fail err => fail err
 | div => div
 | ok ap0 => match FIo_Native.weights.powers 4#usize (epick i.alpha.value 1) with
   | fail err => fail err
   | div => div
   | ok ap1 => NJF_AllocatorInstantiation.G r (context i ap0 ap1)

/-- Whole pair oracle instantiation equals the SAME source invocation. Powers
canonicality is obtained from the CLOSED emitted law, not root premises. -/
theorem source (r : NP6_StdModel.Reservation) (i : Input)
 (domain : NIT_PairDomain.Domain i.owner.value i.alpha.value i.message.value i.kappa) :
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
   exact NJF_AllocatorInstantiation.source r (context i ap0 ap1) domain p0 p1

/-- Printed pair root: native G specializes to the emitted frozen pair body.
The Kani/cut transcriptions are the separately reviewed native half. -/
theorem root (r : NP6_StdModel.Reservation) (i : Input)
 (domain : NIT_PairDomain.Domain i.owner.value i.alpha.value i.message.value i.kappa) :
 (letI:=FIo_Install.allocation r
  FIo_Native.weights.Weights.pair i.owner.value i.alpha.value.to_slice i.message.value i.kappa)=G r i ∧
 NIT_ResultCanonical.Canonical (G r i) := by
 rw [source r i domain]
 exact NIW_AlignPairPhaseSource.source r i domain

#print root
#print axioms source
#print axioms root
end AspisR1.NJF_PairInstantiation
