import NMT_345BoundaryPublicData
import NMT_R2_GetterEquality
set_option autoImplicit false
noncomputable section
namespace NMT_R2_345AtPublicData
open Aeneas Aeneas.Std NMT_345 RSL

def install (keep : Bool) (c : Calls) : Calls :=
 {c with c10 := NMT_R2_EmittedData.clone keep}

/-- One exact E003 getter occurrence; every outer/inner Result is retained. -/
theorem boundary {W : Type} (keep : Bool) (c : Calls) (s : CheckpointData W) :
 raw05 (install keep c) s =
 tryStep (NMT_stage1_owned.r1_pool_adapter.owned.OwnedAccount.data
  (NMT_R2_EmittedData.clone keep) s.publicAccount)
  (fun bytes => raw06 (install keep c) ⟨s,bytes⟩) := boundaryPublicData _ s

theorem observation {W : Type} (keep : Bool) (s : CheckpointData W) (env : Env) :
 NMT_R2.data (account s.publicAccount) env (NMT_R2_EmittedData.run keep s.publicAccount) :=
 NMT_R2_EmittedData.emitted_data keep s.publicAccount env
#print axioms boundary
#print axioms observation
end NMT_R2_345AtPublicData
end
