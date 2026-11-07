import NMT_345RawSelected
import NMT_345Raw_00
import NMT_345Distinct
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result
/-- Isolate only the FIRST native call reply. The entire continuation remains
raw00; no downstream call, allocation or concrete buffer is normalized. -/
theorem boundary_distinct {W : Type} (c : Calls) (s : Selected W) :
 rawSelected c s = tryStep (c.c15 (selectedArray s)) (fun _ => raw00 c s) := by
 unfold rawSelected tryStep selectedArray
 cases h : c.c15 (Array.make 3#usize [s.proofAccount,s.publicAccount,s.checkpointAccount]) with
 | fail e => simp only [h,bind_tc_fail]
 | div => simp only [h,bind_tc_div]
 | ok r =>
  cases r with
  | Err e =>
   simp only [h,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame,Aeneas.Std.core.convert.FromSame.from]
  | Ok u =>
   cases u
   simp only [h,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
   rfl
#print axioms boundary_distinct
end NMT_345
