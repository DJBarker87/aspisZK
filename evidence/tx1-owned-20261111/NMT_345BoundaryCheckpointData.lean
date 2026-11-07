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
theorem boundaryCheckpointData {W : Type} (c : Calls) (s : Selected W) :
 raw03 c s = tryStep (NMT_stage1_owned.r1_pool_adapter.owned.OwnedAccount.data c.c10 s.checkpointAccount) (fun bytes => raw04 c ⟨s,bytes⟩) := by
 unfold raw03 tryStep
 cases h : (NMT_stage1_owned.r1_pool_adapter.owned.OwnedAccount.data c.c10 s.checkpointAccount) with
 | fail e => simp only [h,bind_tc_fail]
 | div => simp only [h,bind_tc_div]
 | ok r =>
  cases r with
  | Err e =>
   simp only [h,bind_tc_ok,Aeneas.Std.core.result.Result.Insts.CoreOpsTry.branch,
    Aeneas.Std.core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    Aeneas.Std.core.convert.FromSame,Aeneas.Std.core.convert.FromSame.from]
  | Ok v =>
   simp only [h,bind_tc_ok,Aeneas.Std.core.result.Result.Insts.CoreOpsTry.branch]
   rfl
#print axioms boundaryCheckpointData
end NMT_345
