import NMS_Owned242Cuts
import NMS_TryFold
set_option autoImplicit false
noncomputable section
namespace NMS_242Tail
open Aeneas Aeneas.Std AdapterRw NMS_OwnedPackets NMS_RowSpec242

def owned {Ambient : Type} (ops : Ops) (inputs : List Nat)
 (request : Request) (auth : Auth) (scanned : Scanned) :
 NMS_Owned242.Run Ambient (NMS_TryFold.R Validated) :=
 NMS_TryFold.step (NMS_Owned242.reconstruct ops inputs request auth scanned.candidate)
  (fun statement => pure (.Ok ⟨statement,scanned.proofLength⟩))

def raw (ops : Ops) (request : Request)
 (auth : r1_pool_adapter.AuthenticatedAsq8Accounts) (scanned : r1_pool_adapter.ScannedAsqaProof) :
 NJU_Log.Run RawEvent (NMS_TryFold.R r1_pool_adapter.ValidatedAsqa) :=
 NMS_TryFold.step
  (NJU_Log.record (NLM_Validate242.Event.reconstruct request auth scanned.candidate_afterstate)
   (ops.op52 request auth scanned.candidate_afterstate))
  (fun statement => pure (.Ok ⟨statement,scanned.proof_length⟩))

theorem erases {Ambient : Type} (ops : Ops) (inputs : List Nat)
 (request : Request) (auth : Auth) (scanned : Scanned) :
 NMS_LogMap.run (Event.erase (Ambient := Ambient)) (NMS_LogMap.rust Validated.erase)
  (owned ops inputs request auth scanned) = raw ops request auth.erase scanned.erase := by
 unfold owned raw
 apply NMS_TryFold.mapped Event.erase Box.payload Validated.erase
 · exact NMS_Owned242Cuts.reconstruct ops inputs request auth scanned.candidate
 · intro statement
   rfl
#print axioms erases
end NMS_242Tail
