import NIW_AlignPairPhaseSource
import NIT_PacketTransport
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignPairInstalled
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_PairControl

def input (w : Ref FIo_Install.W) (alpha : Ref (Array FE 2#usize))
 (f : Ref (Slice U8)) (kappa : FE) (ap0 ap1 common low scratch parts : Nat) : NIW_AlignPairPhase.Input :=
 ⟨⟨w.address,FIo_Install.toWeights w.value⟩,
  ⟨alpha.address,NFW_PowersCohort.mapArray FIo_Install.toE alpha.value⟩,
  f,FIo_Install.toE kappa,ap0,ap1,common,low,scratch,parts⟩

def observed (r : NP6_StdModel.Reservation) (w : Ref FIo_Install.W)
 (alpha : Ref (Array FE 2#usize)) (f : Ref (Slice U8)) (kappa : FE)
 (ap0 ap1 common low scratch parts : Nat) :=
 NIW_AlignPairPhase.run r (input w alpha f kappa ap0 ap1 common low scratch parts)

/-- Installed coordinate transport of the actual collected complete Result.
Every source child has already been discharged; no existential packet result,
endpoint equation or successful child is an input premise. -/
theorem source (r : NP6_StdModel.Reservation) (w : Ref FIo_Install.W)
 (alpha : Ref (Array FE 2#usize)) (f : Ref (Slice U8)) (kappa : FE)
 (ap0 ap1 common low scratch parts : Nat)
 (domain : NIT_PairDomain.Domain (FIo_Install.toWeights w.value)
  (NFW_PowersCohort.mapArray FIo_Install.toE alpha.value) f.value (FIo_Install.toE kappa)) :
 FIo_Install.pair r w.value alpha.value.to_slice f.value kappa=
  NIT_ErrorTransport.full (observed r w alpha f kappa ap0 ap1 common low scratch parts).1 ∧
 NIT_ResultCanonical.Canonical (observed r w alpha f kappa ap0 ap1 common low scratch parts).1 := by
 have actual := NIW_AlignPairPhaseSource.source r (input w alpha f kappa ap0 ap1 common low scratch parts) domain
 refine ⟨?_,actual.2⟩
 unfold FIo_Install.pair
 exact (NIT_PacketTransport.adapter _).trans (congrArg NIT_ErrorTransport.full actual.1)

#print axioms source
end AspisR1.NIW_AlignPairInstalled
