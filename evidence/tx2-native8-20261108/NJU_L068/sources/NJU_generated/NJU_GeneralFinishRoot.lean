import NJU_WeakFinishObserved
import NJU_FinishObserved
import NJU_FinishCaller
import NJU_WeakFinishPort
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJU_GeneralFinishRoot
open Aeneas Aeneas.Std Result AspisR1Stage2 NIT_Cuts NIW_AlignFinishComposed

/-- Generalized full-Result/ordered-effects bridge: exact same native G and
source invocation as NJF_, including malformed-word abort prefixes. The
native cut table is retained, supplemented by NJU's arbitrary-window and
abort controls. No history, NoBad, proof persistence or success premise.
Authoritative row credit waits for the combined audit and next ledger gate. -/
theorem finish (r : NP6_StdModel.Reservation) (loc : Locations) (proof : Slice U8)
 (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
 (facts : NJU_FinishInput.Holds proof v p a) :
 let execution:=NJF_FinishObserved.G r loc v p a
 Port3_NativeFinishBody.verifier.finish_relation (NIG_Slots.installed r) v p a none=execution.1 ∧
 NIW_AlignFinishComposedLog.forget execution=NIW_AlignFinishExecution.run r v p a ∧
 NIW_AlignFinishPrefix.Prefix execution.2.1 := by
 have same:=NJU_WeakFinishObserved.source_log r loc proof v p a facts
 have first:=congrArg Prod.fst same
 change (NJF_FinishObserved.G r loc v p a).1=(NIW_AlignFinishExecution.run r v p a).1 at first
 refine ⟨(NJU_FinishObserved.source r v p a (NJU_FinishInput.intrinsic proof v p a facts)).trans first.symm,same,?_⟩
 have history:=NIW_AlignFinishPrefix.source r v p a
 have events:=congrArg Prod.snd same
 change (NJF_FinishObserved.G r loc v p a).2.1=(NIW_AlignFinishExecution.run r v p a).2 at events
 rw [events]
 exact history

/-- The reviewed returning PairPort cut is retained exactly, with the full
source/nested pair certificate produced internally on the same invocation. -/
theorem ported (r : NP6_StdModel.Reservation) (loc : Locations) (proof : Slice U8)
 (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
 (facts : NJU_FinishInput.Holds proof v p a) (port : PairPort) (afterOwner : Nat)
 (cut : NIW_AlignFinishPort.Cut p port afterOwner (NJF_FinishObserved.G r loc v p a).2.2) :
 let execution:=NJF_FinishObserved.G r loc v p a
 Port3_NativeFinishBody.verifier.finish_relation (NIG_Slots.installed r) v p a none=execution.1 ∧
 NIW_AlignFinishComposedLog.forget execution=NIW_AlignFinishExecution.run r v p a ∧
 NIW_AlignFinishPrefix.Prefix execution.2.1 ∧
 NJU_WeakFinishPairCertificate.Bound r execution.2.2 ∧
 NIW_AlignFinishPort.Bound r port execution.2.2 := by
 obtain ⟨value,events,history⟩:=finish r loc proof v p a facts
 have same:=NJU_WeakFinishObserved.source r loc proof v p a facts
 refine ⟨value,events,history,?_,?_⟩
 · rw [same]
   exact NJU_WeakFinishPairCertificate.source r loc proof v p a facts
 · rw [same] at cut ⊢
   exact NJU_WeakFinishPort.source r loc proof v p a facts port afterOwner cut

#print ported
#print axioms ported
#print finish
#print axioms finish
end AspisR1.NJU_GeneralFinishRoot
