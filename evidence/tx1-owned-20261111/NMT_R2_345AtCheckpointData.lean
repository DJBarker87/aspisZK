import NMT_345BoundaryCheckpointData
import NMT_R2_GetterEquality
set_option autoImplicit false
noncomputable section
namespace NMT_R2_345AtCheckpointData
open Aeneas Aeneas.Std NMT_345 RSL

def install (keep : Bool) (c : Calls) : Calls :=
 {c with c10 := NMT_R2_EmittedData.clone keep}

/-- One exact E003 getter occurrence; every outer/inner Result is retained. -/
theorem boundary {W : Type} (keep : Bool) (c : Calls) (s : Selected W) :
 raw03 (install keep c) s =
 tryStep (NMT_stage1_owned.r1_pool_adapter.owned.OwnedAccount.data
  (NMT_R2_EmittedData.clone keep) s.checkpointAccount)
  (fun bytes => raw04 (install keep c) ⟨s,bytes⟩) := boundaryCheckpointData _ s

theorem observation {W : Type} (keep : Bool) (s : Selected W) (env : Env) :
 NMT_R2.data (account s.checkpointAccount) env (NMT_R2_EmittedData.run keep s.checkpointAccount) :=
 NMT_R2_EmittedData.emitted_data keep s.checkpointAccount env
#print axioms boundary
#print axioms observation
end NMT_R2_345AtCheckpointData
end
