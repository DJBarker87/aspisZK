import NNG_TypedEvents
import NNG_LIBDigest
import NNG_Model134
import NNG_ModelCircle
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_LIBEvents136
open Aeneas Aeneas.Std NNG_verify_finish NNG_Emitted

def events (env : RSL.Env) (event : NMT_CallTree.Event) : List RSL.Event :=
  NNG_TypedEvents.select "rounds"
    (fun (args : r1_wire.Prefix × r1_wire.SemanticTranscript Unit) =>
      LIB_VCode.events env (NNG_Model134.model (NNG_LIBDigest.digest env) args.1 args.2).1) event ++
  NNG_TypedEvents.select "circle0"
    (fun (args : r1_wire.SemanticTranscript Unit × r1_wire.ValidatedRecord) =>
      LIB_VCode.events env (NNG_ModelCircle.model (NNG_LIBDigest.digest env) args.1 args.2).1) event ++
  NNG_TypedEvents.select "circle1"
    (fun (args : r1_wire.SemanticTranscript Unit × r1_wire.ValidatedRecord) =>
      LIB_VCode.events env (NNG_ModelCircle.model (NNG_LIBDigest.digest env) args.1 args.2).1) event

theorem rounds {Reply : Type} (env : RSL.Env) (p : r1_wire.Prefix) (t : r1_wire.SemanticTranscript Unit)
    (reply : Result Reply) :
    events env (.call "rounds" (p,t) reply) =
      LIB_VCode.events env (NNG_Model134.model (NNG_LIBDigest.digest env) p t).1 := by
  simp [events,NNG_TypedEvents.select]
#print axioms rounds

theorem circle0 {Reply : Type} (env : RSL.Env) (t : r1_wire.SemanticTranscript Unit)
    (r : r1_wire.ValidatedRecord) (reply : Result Reply) :
    events env (.call "circle0" (t,r) reply) =
      LIB_VCode.events env (NNG_ModelCircle.model (NNG_LIBDigest.digest env) t r).1 := by
  simp [events,NNG_TypedEvents.select]
#print axioms circle0

theorem circle1 {Reply : Type} (env : RSL.Env) (t : r1_wire.SemanticTranscript Unit)
    (r : r1_wire.ValidatedRecord) (reply : Result Reply) :
    events env (.call "circle1" (t,r) reply) =
      LIB_VCode.events env (NNG_ModelCircle.model (NNG_LIBDigest.digest env) t r).1 := by
  simp [events,NNG_TypedEvents.select]
#print axioms circle1

theorem silent {Args Reply : Type} (env : RSL.Env) (site : String) (args : Args) (reply : Result Reply)
    (r : site ≠ "rounds") (c0 : site ≠ "circle0") (c1 : site ≠ "circle1") :
    events env (.call site args reply) = [] := by
  simp [events,NNG_TypedEvents.select,r,c0,c1]
#print axioms silent
end AspisR1.NNG_LIBEvents136
