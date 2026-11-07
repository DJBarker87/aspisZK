import NMT_345StepBase
import NMT_345Distinct
import NMT_345Raw_03
import NMT_345Raw_04
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result
/-- One actual emitted call occurrence. The suffix stays a named opaque
continuation over the same full parent state; every Result arm is exact. -/
theorem splitCheckpointData {W : Type} (c : Calls) (s : Selected W) :
 raw03 c s = tryStep (NMT_stage1_owned.r1_pool_adapter.owned.OwnedAccount.data c.c10 s.checkpointAccount) (fun bytes => raw04 c ⟨s,bytes⟩) :=
 emitted_try (NMT_stage1_owned.r1_pool_adapter.owned.OwnedAccount.data c.c10 s.checkpointAccount) (fun bytes => raw04 c ⟨s,bytes⟩)
#print axioms splitCheckpointData
end NMT_345
