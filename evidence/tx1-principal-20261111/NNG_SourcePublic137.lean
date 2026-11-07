import NNG_SourceBegin137
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_SourcePublic137
open Aeneas Aeneas.Std Result NMP_prepare NMP_Transport NMT_CallTree NNG_Context137 NNG_Observed136
open NNG_SourceStep136 NNG_DLawStep136

theorem source (a : NNG_Data137.Args) (obs : RSL.Observer) (env : RSL.Env)
    (domain : RSL.TX1_137.Domain NNG_Data137.VL a) (p : LIB_VCarriers.Prefix)
    (parsed : LIB_VParsePrefix.eval a.bytes=.ok p) :
    (RSL.RE.bind (LIB_VLib.library.publicTranscript.run (a.public_,LIB_VCarriers.c1Root p)) fun t0=>
      RSL.RE.bind (LIB_VLib.library.begin.run (p,t0)) fun r=>
      RSL.Spec.call (RSL.TX1_136.Domain LIB_VLib.library) (RSL.TX1_136.Ref LIB_VLib.library)
        ⟨a.public_,p,r.2,r.1⟩) env
      (observation (NNG_Output137.decode a env) (NNG_Events137.events env)
        (NNG_Tree137.publicTranscript (calls env) (input a obs env) (fromT13 (LIB_VCarriers.prefixRaw p)))) := by
  let root := (fromT13 (LIB_VCarriers.prefixRaw p)).c1_root
  let head := invoke "TX1:131/public_transcript" (fromT9 a.public_,(),root)
    (NMP_Install131.publicTranscript (NNG_PublicSource137.digest env) (fromT9 a.public_) () root)
  let k : core.result.Result (r1_wire.SemanticTranscript Unit) r1_wire.Error → Code (Output Unit) := fun reply=>
    match reply with
    | .Err e=>pure (.Err e)
    | .Ok t=>NNG_Tree137.begin_ (calls env) (input a obs env) (fromT13 (LIB_VCarriers.prefixRaw p)) t
  change _ env (observation _ _ (NMT_CallTree.bind head k))
  have headLaw : (LIB_VLib.library.publicTranscript.run (a.public_,LIB_VCarriers.c1Root p)) env
      (observation NNG_PublicProjection137.decode (NNG_Events137.events env) head) := by
    rw [←NNG_Occurrences137.publicTranscript env a.public_ p]
    exact call_actual _ NNG_Events137.events _ _ _ env
  unfold RSL.RE.bind
  refine bind_sound head k NNG_PublicProjection137.decode (NNG_Output137.decode a env)
    (NNG_Events137.events env) env _ _ headLaw ?_
  intro reply returned
  have native := invoke_returned (NNG_Events137.events env) "TX1:131/public_transcript" _ _ _ returned
  cases reply with
  | Err e=>
    change (⟨.ret (NNG_Output137.decode a env (.Err e)),[]⟩ : RSL.Obs _) = ⟨.ret (.error (toT12 e)),[]⟩
    rw [NNG_Head137.error]
  | Ok t=>
    exact NNG_SourceBegin137.source a obs env domain p t parsed (NNG_StageValues137.public_eval env a.public_ p t native)
#print axioms source
end AspisR1.NNG_SourcePublic137
