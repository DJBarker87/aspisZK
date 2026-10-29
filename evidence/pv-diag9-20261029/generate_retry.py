from pathlib import Path
import json
D=Path(__file__).parent
current='PV_DIAG9_Retry'
header='''import PV_DIAG9_Result
import R1Z.ProverCommitRetry34
import R1Z.ProverCommitSemanticTransport26
set_option autoImplicit false
namespace PV_DIAG9
open Aeneas Aeneas.Std Result R1Z
open ProverCommitRetry34
'''
steps=[('retry_terminates','''theorem retry_terminates {S P : Type} (attempt : Attempt S P)
 (terminates : ∀ k s, ∃ v, attempt k s=.ok v) (fuel index : Nat) (s : S) :
 ∃ v, run attempt fuel index s=.ok v := by
 induction fuel generalizing index s with
 | zero => exact ⟨_,rfl⟩
 | succ n ih =>
   obtain ⟨⟨step,after⟩,ha⟩ := terminates index s
   rw [run,ha]
   cases step with
   | done p => exact ⟨_,rfl⟩
   | stop e => exact ⟨_,rfl⟩
   | retry => exact ih (index+1) after'''),
('retry_no_panic','''theorem retry_no_panic {S P : Type} (attempt : Attempt S P)
 (terminates : ∀ k s, ∃ v, attempt k s=.ok v) (fuel index : Nat) (s : S) :
 run attempt fuel index s ≠ .fail .panic :=
 terminating_excludes_panic (retry_terminates attempt terminates fuel index s)'''),
('retry_no_divergence','''theorem retry_no_divergence {S P : Type} (attempt : Attempt S P)
 (terminates : ∀ k s, ∃ v, attempt k s=.ok v) (fuel index : Nat) (s : S) :
 run attempt fuel index s ≠ .div := by
 obtain ⟨v,hv⟩ := retry_terminates attempt terminates fuel index s
 exact ok_excludes_div hv'''),
('cap8_no_panic','''theorem cap8_no_panic {S P : Type} (attempt : Attempt S P)
 (terminates : ∀ k s, ∃ v, attempt k s=.ok v) (s : S) :
 eight attempt s ≠ .fail .panic := retry_no_panic attempt terminates 8 0 s'''),
('rejected_is_normal_result','''theorem rejected_is_normal_result {S P : Type} (s : S) :
 (.ok (classify (.Err .Rejected : Status P),s) : Result (Step P × S)) ≠ .fail .panic :=
 ok_excludes_panic rfl'''),
('exhaustion_is_normal_result','''theorem exhaustion_is_normal_result {S P : Type} (attempt : Attempt S P) (index : Nat) (s : S) :
 run attempt 0 index s ≠ .fail .panic := ok_excludes_panic rfl'''),
('actual_entered_attempt_terminates','''theorem actual_entered_attempt_terminates {S P : Type} (attempt : Attempt S P)
 (fuel index : Nat) (s : S) (out : Step (Published P) × S)
 (h : run attempt (fuel+1) index s=.ok out) : ∃ step after, attempt index s=.ok (step,after) := by
 obtain ⟨⟨step,after⟩,ha,_⟩ := bind_prefix_terminates (attempt index s) _ h
 exact ⟨step,after,ha⟩'''),
('actual_entered_attempt_no_panic','''theorem actual_entered_attempt_no_panic {S P : Type} (attempt : Attempt S P)
 (fuel index : Nat) (s : S) (out : Step (Published P) × S)
 (h : run attempt (fuel+1) index s=.ok out) : attempt index s ≠ .fail .panic := by
 obtain ⟨step,after,ha⟩ := actual_entered_attempt_terminates attempt fuel index s out h
 exact ok_excludes_panic ha'''),
('retry_after_rejected','''theorem retry_after_rejected {S P : Type} (attempt : Attempt S P)
 (fuel index : Nat) (s after : S) (h : attempt index s=.ok (.retry,after)) :
 run attempt (fuel+1) index s=run attempt fuel (index+1) after := by
 rw [run,h]; rfl'''),
('stop_retains_state','''theorem stop_retains_state {S P : Type} (attempt : Attempt S P)
 (fuel index : Nat) (s after : S) (e : Error)
 (h : attempt index s=.ok (.stop e,after)) :
 run attempt (fuel+1) index s=.ok (.stop e,after) := by rw [run,h]; rfl''')]
# Error above must denote retry's verifier error rather than Aeneas.Error.
steps[-1]=(steps[-1][0],steps[-1][1].replace('(e : Error)','(e : ProverCommitRetry34.Error)'))
s=header;cs=[]
for n,d in steps:s+=d+'\n#print axioms '+n+'\n';cs.append(s+'end PV_DIAG9\n')
p=D/'plans.json';j=json.loads(p.read_text());j[current]=cs;p.write_text(json.dumps(j,indent=2)+'\n');(D/(current+'.lean')).write_text(cs[-1])
