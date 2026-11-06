import NLB_ObservedSteps
import NLB_C01Domain
set_option autoImplicit false
noncomputable section
namespace NLB_Parent
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NJU_CommonObserved
/-- Only C01's actual invocation needs a Result projection. C04 is executed
with its native complete Result here; transport to the cohort is separate. -/
theorem target_steps (wr rr fr : NP6_StdModel.Reservation) (loc : NIW_AlignFinishComposed.Locations)
 (nativeResume : Resume) (nativeMerkle : Merkle)
 {H : Type} (d : aspis_core.digest.Digest32 H) (pub proof ck : Slice U8) (hash : H)
 (resumeCall : nativeResume d ck proof pub hash=NJJ_Common.resume wr d ck proof pub .S2 hash)
 (headlineSize : proof.val.length=57607)
 (observe : NKE_QueryInput.Args → QueryObservation)
 (cuts : QueryCuts wr rr fr nativeMerkle d pub proof ck hash observe)
 (e : Event) (entered : e∈(run wr rr nativeMerkle (finish fr) d pub proof ck hash none).events) :
 queryWindow (window rr fr loc nativeResume nativeMerkle d hash) observe e=e := by
 cases e with
 | resume c pr pu r =>
   obtain ⟨hc,hpr,hpu⟩ := NLB_C01Domain.source wr rr nativeMerkle (finish fr) d pub proof ck hash _ entered
   subst c;subst pr;subst pu
   exact C01_step wr rr fr loc nativeResume nativeMerkle nativeMerkle d pub proof ck hash ck proof pub r entered resumeCall
 | query pr p a g geo pending r =>
   exact query_step wr rr fr loc nativeResume nativeMerkle nativeMerkle d pub proof ck hash pr p a g geo pending r entered headlineSize observe (cuts pr p a g geo pending r entered)
 | powers g r => exact C02_step wr rr fr loc nativeResume nativeMerkle nativeMerkle d pub proof ck hash g r entered
 | inactive b r => exact C03_step wr rr fr loc nativeResume nativeMerkle nativeMerkle d pub proof ck hash b r entered
 | merkle pr p root r => exact C04_step wr rr fr loc nativeResume nativeMerkle nativeMerkle d pub proof ck hash pr p root r entered rfl
 | geometry qs n r => exact C05_step wr rr fr loc nativeResume nativeMerkle nativeMerkle d pub proof ck hash qs n r entered
 | pending w r => exact C06_step wr rr fr loc nativeResume nativeMerkle nativeMerkle d pub proof ck hash w r entered
 | flush b w r => exact C08_step wr rr fr loc nativeResume nativeMerkle nativeMerkle d pub proof ck hash b w r entered
 | finish v p a r => exact C09_step wr rr fr loc nativeResume nativeMerkle nativeMerkle d pub proof ck hash v p a r entered
#print axioms target_steps
end NLB_Parent
