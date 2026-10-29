import PV_RJ4IDB_DiagWorld
import PV_DIAG3_Observer
import PV_RJ4IDB_ResultOutput
set_option autoImplicit false
namespace PV_RJ4IDB
open Aeneas Aeneas.Std R1Z.ProverCommitRetry34
variable {H S P : Type}
def observedClient (expose : H → List (Bytes × Bytes))
 (retry : PV_DIAG3.Op H (Result (Step (Published P) × S)))
 (o : PV_DIAG3.ClientHandlers H S P) (h : H) : Observation Nat :=
 decoder (diagWithState expose (PV_DIAG3.clientExecute retry o h))

/-- A source retry leaf is composed with the actual selected continuation;
no normal reporting law is substituted for a failure/divergence prefix. -/
theorem native_normal_model (expose : H → List (Bytes × Bytes))
 (retry : PV_DIAG3.Op H (Result (Step (Published P) × S)))
 (o : PV_DIAG3.ClientHandlers H S P) (a : Attempt S P) (n k : Nat) (state : S)
 (s t : H) (es : List PV_DIAG3.Event)
 (leaf : retry s = ⟨es,t,.value (run a n k state)⟩) :
 observedClient expose retry o s =
 decoder (diagWithState expose (PV_DIAG3.prepend es (PV_DIAG3.modelClient a n k state o t))) := by
 unfold observedClient
 rw [PV_DIAG3.client_native_normal_model retry o a n k state s t es leaf]

/-- Complete returned output travels with its native diagnostic execution.
This conjunction does not infer trace equality from Result equality. -/
theorem result_and_trace (expose : H → List (Bytes × Bytes))
 (retry : PV_DIAG3.Op H (Result (Step (Published P) × S)))
 (o : PV_DIAG3.ClientHandlers H S P) (s : H)
 (r : Result (Step (Published P) × S)) :
 (resultOutput r,observedClient expose retry o s) =
 (resultOutput r,decoder (diagWithState expose (PV_DIAG3.clientExecute retry o s))) := rfl
#print axioms native_normal_model
#print axioms result_and_trace
end PV_RJ4IDB
