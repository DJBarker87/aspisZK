import LIB_VCode
import LIB_VRoundCanonical
set_option autoImplicit false
noncomputable section
namespace LIB_VRounds
open Aeneas Aeneas.Std LIB_VCarriers
open LIB_VScalarCarriers (toRaw ofRaw)
open AspisR1 AspisR1PublicPreparation
def code (a : Prefix × Transcript) (env : RSL.Env) :=
 S1SemanticCode.rounds NJM_RoundJoin.R (LIB_VCode.digest env) (prefixRaw a.1) a.2
def model (a : Prefix × Transcript) (env : RSL.Env) : Result (Except WErr (QM31 × Alpha × Transcript)) :=
 match h : (PreparedHashCode.run (code a env)).2 with
 | .ok (.Ok after) =>
   let canonical := LIB_VRoundCanonical.rounds a.1 (LIB_VCode.digest env) a.2 after h
   .ok (.ok (ofRaw after.1 canonical.1,LIB_VArray.lift after.2.1 canonical.2,after.2.2))
 | .ok (.Err e) => .ok (.error e)
 | .fail e => .fail e
 | .div => .div
def events (a : Prefix × Transcript) (env : RSL.Env) :=
 LIB_VCode.events env (PreparedHashCode.run (code a env)).1
def semanticRounds : RSL.Child (Prefix × Transcript) (Except WErr (QM31 × Alpha × Transcript)) :=
 ⟨fun a=>a.1.source.val.length≤57607,fun a=>LIB_Carriers.resultGraph id (model a) (events a)⟩
def forget : Except WErr (QM31 × Alpha × Transcript) →
 Except WErr (aspis_core.field.QM31 × Array aspis_core.field.QM31 10#usize × Transcript)
 | .ok (q,a,t)=>.ok (toRaw q,alphaRaw a,t)
 | .error e=>.error e
theorem alpha_lift (a : Array aspis_core.field.QM31 10#usize) (h : LIB_VArray.Canonical a) :
 alphaRaw (LIB_VArray.lift a h)=a := LIB_VArray.raw_lift a h
theorem model_exact (a : Prefix × Transcript) (env : RSL.Env) :
 (do let out←model a env;Result.ok (forget out)) =
 (do let out←(PreparedHashCode.run (code a env)).2;Result.ok (LIB_VRecords.host out)) := by
 unfold model
 split <;> simp_all only [forget,LIB_VRecords.host,LIB_VScalarCarriers.toRaw_ofRaw,
  alpha_lift,bind_tc_ok,bind_tc_fail,bind_tc_div]
def eval (a : Prefix × Transcript) (env : RSL.Env) : Except WErr (QM31 × Alpha × Transcript) :=
 LIB_VResult.value id (.error .Terminal) (model a env)
theorem returns (a : Prefix × Transcript) (env : RSL.Env) :
 NND_Returned.Returns (semanticRounds.law a) env (eval a env) :=
 LIB_VResult.returns id (Except.error .Terminal : Except WErr (QM31 × Alpha × Transcript)) (model a) (events a) env
theorem functional : RSL.Child.Functional semanticRounds := fun _ _=>LIB_VResult.functional id _ _
theorem law_exact (a : Prefix × Transcript) (env : RSL.Env) (o : RSL.Obs (Except WErr (QM31 × Alpha × Transcript))) :
 semanticRounds.law a env o ↔ o=LIB_Carriers.resultObs id (events a env) (model a env) := Iff.rfl
#print axioms alpha_lift
#print axioms model_exact
#print axioms returns
#print axioms functional
#print axioms law_exact
end LIB_VRounds
