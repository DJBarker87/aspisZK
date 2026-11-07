import NMT_345StepBase
import NMT_345Distinct
import NMT_345Raw_05
import NMT_345Raw_06
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result
/-- One actual emitted call occurrence. The suffix stays a named opaque
continuation over the same full parent state; every Result arm is exact. -/
theorem splitPublicData {W : Type} (c : Calls) (s : CheckpointData W) :
 raw05 c s = tryStep (NMT_stage1_owned.r1_pool_adapter.owned.OwnedAccount.data c.c10 s.publicAccount) (fun bytes => raw06 c ⟨s,bytes⟩) :=
 emitted_try (NMT_stage1_owned.r1_pool_adapter.owned.OwnedAccount.data c.c10 s.publicAccount) (fun bytes => raw06 c ⟨s,bytes⟩)
#print axioms splitPublicData
end NMT_345
