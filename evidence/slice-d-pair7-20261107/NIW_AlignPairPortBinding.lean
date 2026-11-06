import NIW_AlignPairInstalled
import NIT_FinishComposition
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignPairPortBinding
open Aeneas Aeneas.Std Result NIT_Cuts AspisR1Stage2

/-- Parent return-cut transcription at the SAME actual interpreted complete
pair Result. Abort outcomes have no returning port record. -/
def Cut (r : NP6_StdModel.Reservation) (w : Ref FIo_Install.W)
 (alpha : Ref (Array FE 2#usize)) (f : Ref (Slice U8)) (p : verifier.Prepared)
 (ap0 ap1 common low scratch parts : Nat) (log : PairPort) (afterOwner : Nat) : Prop :=
 match (NIW_AlignPairInstalled.observed r w alpha f p.kappa ap0 ap1 common low scratch parts).1 with
 | fail _ => True
 | div => True
 | ok reply => cutPairPort w.address alpha.address f.address p log (NIT_ErrorTransport.reply reply) afterOwner

/-- No packet witness is selected. This consumes the actual pair certificate's
complete Result and only the parent's native return cut. It does not by itself
identify an unrelated arbitrary raw log with this source invocation. -/
theorem bound (r : NP6_StdModel.Reservation) (w : Ref FIo_Install.W)
 (alpha : Ref (Array FE 2#usize)) (f : Ref (Slice U8)) (p : verifier.Prepared)
 (ap0 ap1 common low scratch parts : Nat) (log : PairPort) (afterOwner : Nat)
 (domain : NIT_PairDomain.Domain (FIo_Install.toWeights w.value)
  (NFW_PowersCohort.mapArray FIo_Install.toE alpha.value) f.value (FIo_Install.toE p.kappa))
 (cut : Cut r w alpha f p ap0 ap1 common low scratch parts log afterOwner) :
 match (NIW_AlignPairInstalled.observed r w alpha f p.kappa ap0 ap1 common low scratch parts).1 with
 | fail err => FIo_Install.pair r w.value alpha.value.to_slice f.value p.kappa=fail err
 | div => FIo_Install.pair r w.value alpha.value.to_slice f.value p.kappa=div
 | ok reply => log.reply=NIT_ErrorTransport.reply reply ∧
   FIo_Install.pair r w.value alpha.value.to_slice f.value p.kappa=ok log.reply := by
 have source := (NIW_AlignPairInstalled.source r w alpha f p.kappa ap0 ap1 common low scratch parts domain).1
 cases result : (NIW_AlignPairInstalled.observed r w alpha f p.kappa ap0 ap1 common low scratch parts).1 with
 | fail err => simpa only [result,NIT_ErrorTransport.full] using source
 | div => simpa only [result,NIT_ErrorTransport.full] using source
 | ok reply =>
  simp only [Cut,result] at cut
  have same := (NIT_FinishComposition.pair_port w.address alpha.address f.address p log _ afterOwner cut).symm
  refine ⟨same,?_⟩
  simpa only [result,NIT_ErrorTransport.full,←same] using source

#print axioms bound
end AspisR1.NIW_AlignPairPortBinding
