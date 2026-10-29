from pathlib import Path
import json
D=Path(__file__).parent
text='''import PV_DIAG9_World
set_option autoImplicit false
namespace PV_DIAG10
open PV_DIAG9
/-! context is the original joint public input/L1 coins/retained prefix AND
option-B world. chargedBad MUST be the original headline's charged union.
These sufficient couplings introduce no new bad event, error charge or T field. -/
def PV_DIAG10_Link_Request {I P B : Type} (context : I → P)
 (chargedBad : I → Prop) (policy : I → FaultHistory → Option (FaultRequest × B)) : Prop :=
 ∀ i j, ¬ chargedBad i → ¬ chargedBad j → context i=context j →
 ∀ h, (policy i h).map Prod.fst=(policy j h).map Prod.fst
def PV_DIAG10_Link_WorldBlind {I P B : Type} (context : I → P)
 (world : I → FaultHistory → FaultRequest → B → FaultReply)
 (publicWorld : P → FaultHistory → FaultRequest → FaultReply) : Prop :=
 ∀ i h q b, world i h q b=publicWorld (context i) h q
def PV_DIAG10_Link_ExecutionHistory {I B : Type} (actual : I → FaultHistory)
 (policy : I → FaultHistory → Option (FaultRequest × B))
 (world : I → FaultHistory → FaultRequest → B → FaultReply) (fuel : Nat) : Prop :=
 ∀ i, actual i=adaptive (policy i) (world i) fuel []
def PV_DIAG10_Link_ChargedBad {I : Type} (chargedBad headlineBad : I → Prop) : Prop :=
 ∀ i, chargedBad i ↔ headlineBad i
'''
steps=[('request_coupling_off_bad','''theorem request_coupling_off_bad {I P B : Type} (context : I → P)
 (chargedBad : I → Prop) (policy : I → FaultHistory → Option (FaultRequest × B))
 (world : I → FaultHistory → FaultRequest → B → FaultReply)
 (publicWorld : P → FaultHistory → FaultRequest → FaultReply)
 (requests : PV_DIAG10_Link_Request context chargedBad policy)
 (blind : PV_DIAG10_Link_WorldBlind context world publicWorld)
 (i j : I) (hi : ¬ chargedBad i) (hj : ¬ chargedBad j) (hc : context i=context j)
 (fuel : Nat) (history : FaultHistory) :
 adaptive (policy i) (world i) fuel history=adaptive (policy j) (world j) fuel history := by
 let publicPolicy := fun h => (policy i h).map Prod.fst
 have left := byte_blind_public_replay (policy i) publicPolicy (world i)
   (publicWorld (context i)) (fun _ => rfl) (blind i) fuel history
 have right := byte_blind_public_replay (policy j) publicPolicy (world j)
   (publicWorld (context j)) (fun h => (requests i j hi hj hc h).symm)
   (blind j) fuel history
 rw [hc] at left
 exact left.trans right.symm'''),
('actual_history_off_bad','''theorem actual_history_off_bad {I P B : Type} (context : I → P)
 (chargedBad : I → Prop) (policy : I → FaultHistory → Option (FaultRequest × B))
 (world : I → FaultHistory → FaultRequest → B → FaultReply)
 (publicWorld : P → FaultHistory → FaultRequest → FaultReply) (actual : I → FaultHistory)
 (fuel : Nat) (requests : PV_DIAG10_Link_Request context chargedBad policy)
 (blind : PV_DIAG10_Link_WorldBlind context world publicWorld)
 (execution : PV_DIAG10_Link_ExecutionHistory actual policy world fuel)
 (i j : I) (hi : ¬ chargedBad i) (hj : ¬ chargedBad j) (hc : context i=context j) :
 actual i=actual j := by
 rw [execution i,execution j]
 exact request_coupling_off_bad context chargedBad policy world publicWorld requests blind i j hi hj hc fuel []'''),
('failure_event_off_bad','''theorem failure_event_off_bad {I : Type} (actual : I → FaultHistory)
 (i j : I) (history : actual i=actual j) :
 failureEvent (actual i) ↔ failureEvent (actual j) := failure_event_transport _ _ history'''),
('complete_reply_content_off_bad','''theorem complete_reply_content_off_bad {I : Type} (actual : I → FaultHistory)
 (i j : I) (history : actual i=actual j) :
 (actual i).map Prod.snd=(actual j).map Prod.snd := congrArg (List.map Prod.snd) history'''),
('fault_metadata_off_bad','''theorem fault_metadata_off_bad {I : Type} (actual : I → FaultHistory)
 (i j : I) (history : actual i=actual j) :
 (actual i).map Prod.fst=(actual j).map Prod.fst := congrArg (List.map Prod.fst) history'''),
('charged_union_preserved','''theorem charged_union_preserved {I : Type} (chargedBad headlineBad : I → Prop)
 (link : PV_DIAG10_Link_ChargedBad chargedBad headlineBad) (i : I)
 (h : ¬ headlineBad i) : ¬ chargedBad i := fun bad => h ((link i).mp bad)'''),
('joint_prefix_decoder_off_bad','''theorem joint_prefix_decoder_off_bad {O : Type}
 (decode : FaultHistory → O) (a b : FaultHistory) (h : a=b) : decode a=decode b :=
 congrArg decode h'''),
('retained_history_never_erased','''theorem retained_history_never_erased {B : Type}
 (policy : FaultHistory → Option (FaultRequest × B))
 (world : FaultHistory → FaultRequest → B → FaultReply)
 (fuel : Nat) (before : FaultHistory) :
 ∃ suffix, adaptive policy world fuel before=before++suffix :=
 adaptive_prefix_retained policy world fuel before''')]
for field,typ in [('operation','Nat'),('target','List Nat'),('offset','Nat'),('size','Nat'),('alignment','Nat'),('addressClass','Nat'),('retryState','Nat')]:
 steps.append(('request_'+field+'_retained',f'''theorem request_{field}_retained (q r : FaultRequest) (h : q=r) :
 q.{field}=r.{field} := congrArg FaultRequest.{field} h'''))
plans=[]
for name,decl in steps:
 text+=decl+'\n#print axioms '+name+'\n';plans.append(text+'end PV_DIAG10\n')
(D/'requests-plans.json').write_text(json.dumps({'PV_DIAG10_Requests':plans},indent=2)+'\n')
(D/'PV_DIAG10_Requests.lean').write_text(plans[-1])
