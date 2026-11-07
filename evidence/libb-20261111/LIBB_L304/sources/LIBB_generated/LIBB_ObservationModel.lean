import LIBB_ParserGraph

import LIBB_ObservationPieces
import NNC_WeakSpec
set_option autoImplicit false
noncomputable section
namespace LIBB_ObservationModel
open Aeneas Aeneas.Std AspisR1 VTop_Stages NJU_CommonObserved
/-- Full source observation relation. The resolved arm evaluates the fixed
source Result. Independently stopped C04 arms contain only the chronological
prefix and the answered part of the pending call, never its ideal suffix. -/
def Common (env : RSL.Env) (pub proof ck : Slice U8)
 (o : RSL.Obs (Except LIBB_V2Carriers.VErr Unit)) : Prop :=
 (o.exit=NNC_WeakSpec.resultExit (LIBB_Tx2EnvCode.common env pub proof ck) ∧
  LIBB_ObservationPieces.Pieces env (LIBB_Tx2EnvCode.observed env pub proof ck).events o.events) ∨
 ∃ before pr p folded reply suffix prior inside,
  (LIBB_Tx2EnvCode.observed env pub proof ck).events=
   before++Event.merkle pr p folded reply::suffix ∧
  LIBB_ObservationPieces.Pieces env before prior ∧
  LIBB_ObservationPieces.Prefix env (Event.merkle pr p folded reply) inside ∧
  o=⟨.abort,prior++inside⟩

def law (pub proof ck : Slice U8) : RSL.Spec (Except LIBB_V2Carriers.VErr Unit) :=
 fun env o=> match NLE_ParseInstall.parse proof with
 | .ok (.Ok _) => Common env pub proof ck o
 | _ => o=LIBB_Tx2EnvTrace.observation env pub proof ck

def convert : LIBB_Tx2EnvCode.Reply → Except LIBB_V2Carriers.VErr Unit
 | .Ok () => .ok ()
 | .Err e => .error e

theorem result_exit (r : Result LIBB_Tx2EnvCode.Reply) (events : List RSL.Event) :
 (LIB_Carriers.resultObs convert events r).exit=NNC_WeakSpec.resultExit r := by
 cases r with
 | fail e => rfl
 | div => rfl
 | ok reply => cases reply with | Ok u => cases u;rfl | Err e => rfl

theorem result_events (r : Result LIBB_Tx2EnvCode.Reply) (events : List RSL.Event) :
 (LIB_Carriers.resultObs convert events r).events=events := by
 cases r <;> rfl

theorem observation_exit (env : RSL.Env) (pub proof ck : Slice U8) :
 (LIBB_Tx2EnvTrace.observation env pub proof ck).exit=
 NNC_WeakSpec.resultExit (LIBB_Tx2EnvCode.code env pub proof ck) :=
 result_exit _ _

theorem parsed_observation (env : RSL.Env) (pub proof ck : Slice U8)
 (v : transport.Variant) (parsed : NLE_ParseInstall.parse proof=.ok (.Ok v)) :
 LIBB_Tx2EnvTrace.observation env pub proof ck=
 LIB_Carriers.resultObs convert (LIBB_Tx2EnvTrace.common env pub proof ck)
  (LIBB_Tx2EnvCode.common env pub proof ck) := by
 unfold LIBB_Tx2EnvTrace.observation
 rw [LIBB_ParserGraph.source,parsed]
 unfold LIBB_Tx2EnvTrace.events
 rw [parsed]

theorem common_graph (env : RSL.Env) (pub proof ck : Slice U8) :
 Common env pub proof ck
 (LIB_Carriers.resultObs convert (LIBB_Tx2EnvTrace.common env pub proof ck)
  (LIBB_Tx2EnvCode.common env pub proof ck)) := by
 apply Or.inl
 constructor
 · exact result_exit _ _
 · rw [result_events]
   exact LIBB_ObservationPieces.complete env _

theorem contains_graph (env : RSL.Env) (pub proof ck : Slice U8) :
 law pub proof ck env (LIBB_Tx2EnvTrace.observation env pub proof ck) := by
 unfold law
 cases parsed : NLE_ParseInstall.parse proof with
 | fail e => rfl
 | div => rfl
 | ok r => cases r with
   | Err e => rfl
   | Ok v =>
    rw [parsed_observation env pub proof ck v parsed]
    exact common_graph env pub proof ck

/-- Returned values are unchanged by every independently stopped prefix. -/
theorem returns (env : RSL.Env) (pub proof ck : Slice U8) :
 NND_Returned.Returns (law pub proof ck) env (LIBB_EnvValues.evaluator env pub proof ck) := by
 intro o r observed returned
 have resolved : (LIBB_Tx2EnvTrace.observation env pub proof ck).exit=.ret r := by
  unfold law at observed
  cases parsed : NLE_ParseInstall.parse proof with
  | fail e => rw [parsed] at observed; exact observed ▸ returned
  | div => rw [parsed] at observed; exact observed ▸ returned
  | ok v => cases v with
    | Err e => rw [parsed] at observed; exact observed ▸ returned
    | Ok v =>
     rw [parsed] at observed
     rcases observed with done | ⟨before,pr,p,folded,reply,suffix,prior,inside,_,_,_,rfl⟩
     · rw [observation_exit,LIBB_ParserGraph.source,parsed]
       exact done.1.symm.trans returned
     · cases returned
 exact LIBB_EnvValues.returns pub proof ck env _ r rfl resolved
#print axioms result_exit
#print axioms result_events
#print axioms observation_exit
#print axioms parsed_observation
#print axioms common_graph
#print axioms contains_graph
#print axioms returns
end LIBB_ObservationModel
end
