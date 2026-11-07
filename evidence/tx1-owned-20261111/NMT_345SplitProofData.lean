import NMT_345StepBase
import NMT_345Distinct
import NMT_345Raw_09
import NMT_345Raw_10
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result
/-- One actual emitted call occurrence. The suffix stays a named opaque
continuation over the same full parent state; every Result arm is exact. -/
theorem splitProofData {W : Type} (c : Calls) (s : Candidate W) :
 raw09 c s = tryStep (NMT_stage1_owned.r1_pool_adapter.owned.OwnedAccount.data c.c10 s.proofAccount) (fun bytes => raw10 c ⟨s,bytes⟩) :=
 emitted_try _ _
#print axioms splitProofData
end NMT_345
