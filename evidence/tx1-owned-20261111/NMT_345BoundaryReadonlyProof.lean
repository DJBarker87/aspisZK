import NMT_345StepBase
import NMT_345Distinct
import NMT_345Raw_00
import NMT_345Raw_01
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result
/-- One actual emitted call occurrence. The suffix stays a named opaque
continuation over the same full parent state; every Result arm is exact. -/
theorem boundaryReadonlyProof {W : Type} (c : Calls) (s : Selected W) :
 raw00 c s = tryStep (c.c13 s.proofAccount) (fun _ => raw01 c s) := by
 unfold raw00 tryStep
 cases h : (c.c13 s.proofAccount) with
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
#print axioms boundaryReadonlyProof
end NMT_345
