import NMT_345MapValidator
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result NMT_stage1_owned

theorem map_validator_step {W : Type} (c : Calls) (s : ValidationReply W) :
 mapValidator c s = tryStep
  (c.c2 r1_pool_adapter.owned.stage1_owned.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError s.reply ())
  (fun _ => raw08 c s.toDecoded) := by
 unfold mapValidator tryStep
 cases h : (c.c2 r1_pool_adapter.owned.stage1_owned.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError s.reply ()) with
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

#print axioms map_validator_step
end NMT_345
