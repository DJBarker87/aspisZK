import PV_RJ4IDB_ResultChannels
import R1Z.ProverCommitRetry34
set_option autoImplicit false
namespace PV_RJ4IDB
open Aeneas Aeneas.Std R1Z.ProverCommitRetry34
inductive ReturnedOutput (P : Type) where
 | done (proof : P) (attempts : Nat)
 | retry
 | stop (error : R1Z.ProverCommitRetry34.Error)
 | failed (error : Aeneas.Std.Error)
 | diverge

def resultOutput {P S : Type} : Result (Step (Published P) × S) → ReturnedOutput P
 | .ok (.done p,_) => .done p.proof p.attempts
 | .ok (.retry,_) => .retry
 | .ok (.stop e,_) => .stop e
 | .fail e => .failed e
 | .div => .diverge

/-- This component retains the complete returned tag/proof/count. It makes no
claim that the returned value determines earlier files, time, or diagnostics. -/
theorem resultOutput_map {P S T : Type} (project : S → T)
 (out : Result (Step (Published P) × S)) :
 resultOutput out = resultOutput (R1Z.ProverCommitSemanticTransport26.mapR
 (fun p => (p.1,project p.2)) out) := by
 cases out with
 | fail e => rfl
 | div => rfl
 | ok pair => rcases pair with ⟨step,state⟩; cases step <;> rfl

theorem count_retained {P S : Type} (proof : P) (count : Nat) (s : S) :
 resultOutput (.ok (.done ⟨proof,count⟩,s)) = .done proof count := rfl

theorem returned_output_fibres {W C P : Type}
 (reachable : R1Z.PV_W_Threading.Run W C Aeneas.Std.Error (Step (Published P)) → Prop) :
 R1Z.PV_RJDec_Factor.Fibres reachable (fun r => resultOutput
 (R1Z.PV_RunJoin_WorldDecode33.returned r)) := returned_component reachable resultOutput
#print axioms resultOutput_map
#print axioms count_retained
#print axioms returned_output_fibres
end PV_RJ4IDB
