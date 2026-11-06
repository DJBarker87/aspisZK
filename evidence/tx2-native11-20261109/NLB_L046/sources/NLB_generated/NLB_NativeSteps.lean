import NLB_TargetSteps
import NLB_NativeFlush
set_option autoImplicit false
noncomputable section
namespace NLB_Parent
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NJU_CommonObserved

def flushWindow (base : Event → Event) : Event → Event
 | .flush pending weights _ => .flush pending weights (ok (NLB_NativeFlush.G pending weights))
 | e => base e

/-- Native C08 fold replaces the source endpoint in the forward interpreter;
all other sites retain their individually established SAME-occurrence steps. -/
theorem native_steps (wr rr fr : NP6_StdModel.Reservation) (loc : NIW_AlignFinishComposed.Locations)
 (nativeResume : Resume) (nativeMerkle : Merkle)
 {H : Type} (d : aspis_core.digest.Digest32 H) (pub proof ck : Slice U8) (hash : H)
 (resumeCall : nativeResume d ck proof pub hash=NJJ_Common.resume wr d ck proof pub .S2 hash)
 (headlineSize : proof.val.length=57607)
 (observe : NKE_QueryInput.Args → QueryObservation)
 (cuts : QueryCuts wr rr fr nativeMerkle d pub proof ck hash observe)
 (e : Event) (entered : e∈(run wr rr nativeMerkle (finish fr) d pub proof ck hash none).events) :
 flushWindow (queryWindow (window rr fr loc nativeResume nativeMerkle d hash) observe) e=e := by
 cases e with
 | flush b w r =>
   change Event.flush b w (ok (NLB_NativeFlush.G b w))=_
   rw [NLB_NativeFlush.at_actual wr rr nativeMerkle (finish fr) d pub proof ck hash b w r entered]
 | resume c pr pu r => exact target_steps wr rr fr loc nativeResume nativeMerkle d pub proof ck hash resumeCall headlineSize observe cuts _ entered
 | powers g r => exact target_steps wr rr fr loc nativeResume nativeMerkle d pub proof ck hash resumeCall headlineSize observe cuts _ entered
 | inactive b r => exact target_steps wr rr fr loc nativeResume nativeMerkle d pub proof ck hash resumeCall headlineSize observe cuts _ entered
 | merkle pr p root r => exact target_steps wr rr fr loc nativeResume nativeMerkle d pub proof ck hash resumeCall headlineSize observe cuts _ entered
 | geometry qs n r => exact target_steps wr rr fr loc nativeResume nativeMerkle d pub proof ck hash resumeCall headlineSize observe cuts _ entered
 | pending w r => exact target_steps wr rr fr loc nativeResume nativeMerkle d pub proof ck hash resumeCall headlineSize observe cuts _ entered
 | query pr p a g geo pending r => exact target_steps wr rr fr loc nativeResume nativeMerkle d pub proof ck hash resumeCall headlineSize observe cuts _ entered
 | finish v p a r => exact target_steps wr rr fr loc nativeResume nativeMerkle d pub proof ck hash resumeCall headlineSize observe cuts _ entered
#print axioms native_steps
end NLB_Parent
