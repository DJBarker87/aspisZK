import NMT_345StepBase
import NMT_345Distinct
import NMT_345Raw_02
import NMT_345Raw_03
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result
/-- One actual emitted call occurrence. The suffix stays a named opaque
continuation over the same full parent state; every Result arm is exact. -/
theorem boundaryCheckpoint {W : Type} (c : Calls) (s : Selected W) :
 raw02 c s = tryStep (c.c14 s.checkpointAccount s.program true) (fun _ => raw03 c s) := by
 unfold raw02 tryStep
 cases h : (c.c14 s.checkpointAccount s.program true) with
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
#print axioms boundaryCheckpoint
end NMT_345
