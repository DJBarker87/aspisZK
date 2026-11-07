import NNG_FrontProjection087
import NNG_Canonical087
import NNG_MapError087
import NNG_ResultBind137
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_SourceObserved087
open Aeneas Aeneas.Std Result NMP_prepare NMT_CallTree NNG_Observed136
abbrev Args := NNG_PrepareInput087.Args

theorem source (a : Args) (obs : RSL.Observer) (env : RSL.Env) (v : verifier.View)
 (domain : RSL.TX1_087.Domain LIB_Instances.VL a obs) (size : v.semantic.val.length≤57607) :
 NNG_Canonical087.observed LIB_Instances.VL a (NNG_PrepareCarriers087.view v) env
  (observation (NNG_FrontProjection087.port a env) (NNG_Events087.events env)
   (NNG_Front087.observed (NNG_PrepareEmission087.calls env) (NNG_PrepareInput087.input a obs env) v)) := by
 let head := invoke "TX1:137/verify_observed"
   ((NNG_PrepareInput087.input a obs env).publicValue,v.semantic,(),NNG_Context137.observer obs)
   (NMP_Emitted.observed (NNG_PrepareEmission087.calls env) {(NNG_PrepareInput087.input a obs env) with bytes:=v.semantic})
 let k : NMP_Emitted.SemanticOut Unit → Code (NNG_Front087.FrontOut Unit) := fun r=>
   match r with | .Err _=>pure (.Err verifier.Error.Semantic) | .Ok sem=>pure (.Ok (sem,v))
 have split : NNG_Front087.observed (NNG_PrepareEmission087.calls env) (NNG_PrepareInput087.input a obs env) v = NMT_CallTree.bind head k := rfl
 rw [split]
 have law := NNG_MapError087.law (fun _ : LIB_Instances.VL.WErr => LIB_Instances.VL.vSemantic)
   (NNG_Output137.decode (NNG_ObservedInput087.child a v) env) (NNG_Events087.events env) head env
   (RSL.Spec.call (RSL.TX1_137.Domain LIB_Instances.VL) (RSL.TX1_137.Ref LIB_Instances.VL) (NNG_ObservedInput087.child a v))
   (NNG_ObservedInput087.occurrence a v obs env domain size)
 unfold NNG_Canonical087.observed
 refine NNG_ResultBind137.sound head k
   (fun r=>NNG_MapError087.mapError (fun _ : LIB_Instances.VL.WErr => LIB_Instances.VL.vSemantic)
     (NNG_Output137.decode (NNG_ObservedInput087.child a v) env r))
   (NNG_FrontProjection087.port a env) (NNG_Events087.events env) env _ _ law ?_
 intro reply returned
 cases reply with
 | Err e=>rfl
 | Ok sem=>rfl
#print axioms source
end AspisR1.NNG_SourceObserved087
