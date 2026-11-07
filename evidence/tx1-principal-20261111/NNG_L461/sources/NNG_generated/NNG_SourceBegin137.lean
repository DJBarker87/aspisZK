import NNG_FinishOccurrence137
import NNG_Head137
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_SourceBegin137
open Aeneas Aeneas.Std Result NMP_prepare NMP_Transport NMT_CallTree NNG_Context137 NNG_Observed136
open NNG_SourceStep136 NNG_DLawStep136

theorem source (a : NNG_Data137.Args) (obs : RSL.Observer) (env : RSL.Env)
    (domain : RSL.TX1_137.Domain NNG_Data137.VL a) (p : LIB_VCarriers.Prefix)
    (t0 : r1_wire.SemanticTranscript Unit)
    (parsed : LIB_VParsePrefix.eval a.bytes=.ok p)
    (transcripted : LIB_VPublicTranscript.eval (a.public_,LIB_VCarriers.c1Root p) env=.ok (toT10 t0)) :
    (RSL.RE.bind (LIB_VLib.library.begin.run (p,toT10 t0)) fun r=>
      RSL.Spec.call (RSL.TX1_136.Domain LIB_VLib.library) (RSL.TX1_136.Ref LIB_VLib.library)
        ⟨a.public_,p,r.2,r.1⟩) env
      (observation (NNG_Output137.decode a env) (NNG_Events137.events env)
        (NNG_Tree137.begin_ (calls env) (input a obs env) (fromT13 (LIB_VCarriers.prefixRaw p)) t0)) := by
  let head := invoke "TX1:150/begin" (fromT13 (LIB_VCarriers.prefixRaw p),t0)
    (NMP_Install150.begin_ (NNG_PublicSource137.digest env) (fromT13 (LIB_VCarriers.prefixRaw p)) t0)
  let k : (core.result.Result aspis_core.state_only_prefix.r0.Challenges r1_wire.Error × r1_wire.SemanticTranscript Unit) → Code (Output Unit) := fun pair=>
    match pair.1 with
    | .Err e=>pure (.Err e)
    | .Ok c=>NNG_Tree137.mark1 (calls env) (input a obs env) (fromT13 (LIB_VCarriers.prefixRaw p)) pair.2 c
  change (_ : RSL.Spec (Except LIB_VLib.library.WErr (RSL.Verified LIB_VLib.library))) env (observation _ _ (NMT_CallTree.bind head k))
  have borrow := LIB_VDomains.eval_prefix_bound a.bytes domain.2 p parsed
  have headLaw : (LIB_VLib.library.begin.run (p,toT10 t0)) env
      (observation (NNG_BeginProjection137.decode (NNG_Data137.fallback a env)) (NNG_Events137.events env) head) := by
    change LIB_VBegin.begin_.run (p,toT10 t0) env _
    have law := NNG_Occurrences137.begin_ (NNG_Data137.fallback a env) env p (toT10 t0) borrow
    rw [toT10_inverse] at law
    rw [←law]
    exact call_actual _ NNG_Events137.events _ _ _ env
  unfold RSL.RE.bind
  refine bind_sound head k (NNG_BeginProjection137.decode (NNG_Data137.fallback a env))
    (NNG_Output137.decode a env) (NNG_Events137.events env) env _ _ headLaw ?_
  intro pair returned
  rcases pair with ⟨reply,after⟩
  have native := invoke_returned (NNG_Events137.events env) "TX1:150/begin" _ _ _ returned
  cases reply with
  | Err e=>
    change (⟨.ret (NNG_Output137.decode a env (.Err e)),[]⟩ : RSL.Obs _) = ⟨.ret (.error (toT12 e)),[]⟩
    rw [NNG_Head137.error]
  | Ok rawc=>
    let c := NNG_ChallengeProjection137.project (NNG_Data137.fallback a env) (toT3 rawc)
    have begun := NNG_StageValues137.begin_eval (NNG_Data137.fallback a env) env p t0 rawc after native
    have raw := NNG_Reached137.begin_raw (NNG_Data137.fallback a env) env p t0 rawc after native
    have challenge : fromT3 (LIB_VCarriers.challengesRaw c)=rawc := by
      rw [raw,toT3_inverse]
    have fallback := NNG_Caller136From137.fallback_exact a env p (toT10 t0) c (toT10 after) parsed transcripted begun
    have childDomain := NNG_Caller136From137.finish_domain a env domain p (toT10 t0) c (toT10 after) parsed transcripted begun
    change (RSL.Spec.call (RSL.TX1_136.Domain LIB_VLib.library) (RSL.TX1_136.Ref LIB_VLib.library) ⟨a.public_,p,toT10 after,c⟩) env
      (observation _ _ (NNG_Tree137.mark1 (calls env) (input a obs env) (fromT13 (LIB_VCarriers.prefixRaw p)) after rawc))
    unfold NNG_Tree137.mark1
    change (_ : RSL.Spec (Except LIB_VLib.library.WErr (RSL.Verified LIB_VLib.library))) env (observation _ _ (NMT_CallTree.bind (invoke "TX1:130/mark1" ((input a obs env).observer,1#u8) (.ok ())) (fun _=>_)))
    rw [NNG_Head137.mark _ env _ _ _ (NNG_Events137.silent env _ _ _ (by decide) (by decide) (by decide))]
    have finish := NNG_FinishOccurrence137.occurrence a env p (toT10 after) c obs childDomain fallback
    rw [toT10_inverse,challenge] at finish
    exact finish
#print axioms source
end AspisR1.NNG_SourceBegin137
