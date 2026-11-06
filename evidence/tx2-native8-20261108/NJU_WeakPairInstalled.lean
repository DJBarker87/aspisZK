import NIW_AlignPairInstalled
import NJU_WeakPairCaller
import NJU_WeakPairInstantiation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJU_WeakPairInstalled
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_PairControl
open NIW_AlignPairInstalled

/- Generalized existing evaluator on arbitrary raw words; data/log definitions reused. -/
theorem source (r : NP6_StdModel.Reservation) (w : Ref FIo_Install.W)
 (alpha : Ref (Array FE 2#usize)) (f : Ref (Slice U8)) (kappa : FE)
 (ap0 ap1 common low scratch parts : Nat)
 (domain : NJU_WeakPairDomain.Domain (FIo_Install.toWeights w.value)
  (NFW_PowersCohort.mapArray FIo_Install.toE alpha.value) f.value (FIo_Install.toE kappa)) :
 FIo_Install.pair r w.value alpha.value.to_slice f.value kappa=
  NIT_ErrorTransport.full (observed r w alpha f kappa ap0 ap1 common low scratch parts).1 ∧
 NIT_ResultCanonical.Canonical (observed r w alpha f kappa ap0 ap1 common low scratch parts).1 := by
 have actual := NJU_WeakAlignPairPhaseSource.source r (input w alpha f kappa ap0 ap1 common low scratch parts) domain
 refine ⟨?_,actual.2⟩
 unfold FIo_Install.pair
 exact (NIT_PacketTransport.adapter _).trans (congrArg NIT_ErrorTransport.full actual.1)

#print axioms source
end AspisR1.NJU_WeakPairInstalled
