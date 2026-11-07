import LIB_VCode
import LIB_VChallenges
import NHG_BeginFrame
set_option autoImplicit false
noncomputable section
namespace LIB_VBegin
open Aeneas Aeneas.Std LIB_VCarriers
open AspisR1 AspisR1PublicPreparation
def model (a : Prefix × Transcript) (env : RSL.Env) :
 Result (Except WErr (Challenges × Transcript)) :=
 match h : r1_wire.begin (LIB_VCode.digest env) (prefixRaw a.1) a.2 with
 | .ok (.Ok c,after) => .ok (.ok (LIB_VChallenges.lift c
    (LIB_VChallenges.begin_canonical (LIB_VCode.digest env) a.1 a.2 after c h),after))
 | .ok (.Err e,_) => .ok (.error e)
 | .fail e => .fail e
 | .div => .div
def code (a : Prefix × Transcript) (env : RSL.Env) :=
 NHG_BeginPackets.begin S1SemanticCode.semanticValidated (LIB_VCode.digest env) (prefixRaw a.1) a.2
def events (a : Prefix × Transcript) (env : RSL.Env) :=
 LIB_VCode.events env (PreparedHashCode.run (code a env)).1
def begin_ : RSL.Child (Prefix × Transcript) (Except WErr (Challenges × Transcript)) :=
 ⟨fun a=>a.1.source.val.length≤57607,
  fun a=>LIB_Carriers.resultGraph id (model a) (events a)⟩
def forget : Except WErr (Challenges × Transcript) → Except WErr (r1_wire.Challenges × Transcript)
 | .ok (c,t) => .ok (challengesRaw c,t)
 | .error e => .error e
def project (r : core.result.Result r1_wire.Challenges WErr × Transcript) : Except WErr (r1_wire.Challenges × Transcript) :=
 match r.1 with | .Ok c=>.ok (c,r.2) | .Err e=>.error e
theorem model_exact (a : Prefix × Transcript) (env : RSL.Env) :
 (do let out←model a env;Result.ok (forget out)) =
 (do let out←r1_wire.begin (LIB_VCode.digest env) (prefixRaw a.1) a.2;Result.ok (project out)) := by
 unfold model
 split <;> simp_all only [forget,project,LIB_VChallenges.raw_lift,bind_tc_ok,bind_tc_fail,bind_tc_div]
theorem effects_exact (a : Prefix × Transcript) (env : RSL.Env) :
 events a env = LIB_VCode.events env (PreparedHashCode.run
 (S1SemanticCode.begin (LIB_VCode.digest env) (prefixRaw a.1) a.2)).1 := by
 exact congrArg (LIB_VCode.events env) (NHG_BeginFrame.effects _ _ _)
def eval (a : Prefix × Transcript) (env : RSL.Env) : Except WErr (Challenges × Transcript) :=
 LIB_VResult.value id (.error .Terminal) (model a env)
theorem returns (a : Prefix × Transcript) (env : RSL.Env) :
 NND_Returned.Returns (begin_.law a) env (eval a env) :=
 LIB_VResult.returns id (Except.error .Terminal : Except WErr (Challenges × Transcript)) (model a) (events a) env
theorem functional : RSL.Child.Functional begin_ := fun _ _ => LIB_VResult.functional id _ _
theorem law_exact (a : Prefix × Transcript) (env : RSL.Env) (o : RSL.Obs (Except WErr (Challenges × Transcript))) :
 begin_.law a env o ↔ o=LIB_Carriers.resultObs id (events a env) (model a env) := Iff.rfl
#print axioms model_exact
#print axioms effects_exact
#print axioms returns
#print axioms functional
#print axioms law_exact
end LIB_VBegin
