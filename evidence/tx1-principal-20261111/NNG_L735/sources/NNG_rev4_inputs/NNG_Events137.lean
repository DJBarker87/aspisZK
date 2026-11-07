import NNG_Tree137
import NNG_TypedEvents
import NNG_FinalEvents136
import NNG_PublicProjection137
import NNG_BeginProjection137
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Events137
open Aeneas Aeneas.Std NMP_prepare NMP_Transport
abbrev FinishArgs := NMP_Emitted.Public × r1_wire.Prefix × r1_wire.SemanticTranscript Unit ×
  aspis_core.state_only_prefix.r0.Challenges × NMP_Emitted.Observer

def finish (env : RSL.Env) (a : FinishArgs) : List RSL.Event :=
  (NMT_CallTree.run (NNG_FinishTree.tree (NNG_ConcreteCalls136.calls env)
    (NNG_FinishAdapter137.childInput (NNG_PublicSource137.digest env) (toT9 a.1) (toT13 a.2.1)
      (toT10 a.2.2.1) (toT3 a.2.2.2.1) a.2.2.2.2))).2.flatMap (NNG_FinalEvents136.events env)

def events (env : RSL.Env) (event : NMT_CallTree.Event) : List RSL.Event :=
  NNG_TypedEvents.select "TX1:131/public_transcript"
    (fun (a : NMP_Emitted.Public × Unit × Array U8 32#usize) =>
      LIB_VCode.events env (AspisR1PublicPreparation.PreparedHashCode.run
        (AspisR1PublicPreparation.S1SemanticCode.publicTranscript (LIB_VCode.digest env) (toT9 a.1) () a.2.2)).1) event ++
  NNG_TypedEvents.select "TX1:150/begin"
    (fun (a : r1_wire.Prefix × r1_wire.SemanticTranscript Unit) =>
      LIB_VCode.events env (AspisR1PublicPreparation.PreparedHashCode.run
        (AspisR1PublicPreparation.S1SemanticCode.begin (LIB_VCode.digest env) (toT13 a.1) (toT10 a.2))).1) event ++
  NNG_TypedEvents.select "TX1:136/verify_finish" (finish env) event

theorem public_call {Reply : Type} (env : RSL.Env) (pub : NMP_Emitted.Public) (root : Array U8 32#usize)
    (reply : Result Reply) : events env (.call "TX1:131/public_transcript" (pub,(),root) reply) =
    LIB_VCode.events env (AspisR1PublicPreparation.PreparedHashCode.run
      (AspisR1PublicPreparation.S1SemanticCode.publicTranscript (LIB_VCode.digest env) (toT9 pub) () root)).1 := by
  simp [events,NNG_TypedEvents.select]
#print axioms public_call

theorem begin_call {Reply : Type} (env : RSL.Env) (p : r1_wire.Prefix) (t : r1_wire.SemanticTranscript Unit)
    (reply : Result Reply) : events env (.call "TX1:150/begin" (p,t) reply) =
    LIB_VCode.events env (AspisR1PublicPreparation.PreparedHashCode.run
      (AspisR1PublicPreparation.S1SemanticCode.begin (LIB_VCode.digest env) (toT13 p) (toT10 t))).1 := by
  simp [events,NNG_TypedEvents.select]
#print axioms begin_call

theorem finish_call {Reply : Type} (env : RSL.Env) (a : FinishArgs) (reply : Result Reply) :
    events env (.call "TX1:136/verify_finish" a reply)=finish env a := by
  simp [events,NNG_TypedEvents.select]
#print axioms finish_call

theorem silent {Args Reply : Type} (env : RSL.Env) (site : String) (a : Args) (reply : Result Reply)
    (h0 : site ≠ "TX1:131/public_transcript") (h1 : site ≠ "TX1:150/begin")
    (h2 : site ≠ "TX1:136/verify_finish") : events env (.call site a reply)=[] := by
  simp [events,NNG_TypedEvents.select,h0,h1,h2]
#print axioms silent
end AspisR1.NNG_Events137
