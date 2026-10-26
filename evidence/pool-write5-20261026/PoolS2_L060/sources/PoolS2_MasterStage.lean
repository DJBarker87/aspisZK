import PoolS2_MasterCuts
import PoolS2_Prefix
set_option autoImplicit false
noncomputable section
namespace AspisR1.PoolS2_MasterStage
open Aeneas Aeneas.Std Result PoolS2_PdaSource

/-- Partial owned VALUE/ERROR stage, not the native planner: metadata prefix
then its SAME selected master read. Planner alias/lanes/allocation/System/
borrow/cleanup/query joins remain explicit later obligations. -/
def run (decode : PoolS2_MasterRead.Decode) (pda : Ops) (program : Key)
    (accounts : Slice AdapterRw.Cuts.Account) (data : Slice U8) :
    Result (core.result.Result (PoolS2_Prefix.Roles × Master) AdapterRw.solana_program_error.ProgramError) := do
  let front ← PoolS2_Prefix.run accounts data
  match front with
  | .Err e => ok (.Err e)
  | .Ok roles =>
    let read ← PoolS2_MasterRead.run decode pda program roles.master true
    match read with
    | .Err e => ok (.Err e)
    | .Ok master => ok (.Ok (roles,master))

theorem accepted (decode : PoolS2_MasterRead.Decode) (pda : Ops) (program : Key)
    (accounts : Slice AdapterRw.Cuts.Account) (data : Slice U8) (r : PoolS2_Prefix.Roles) (m : Master)
    (h : run decode pda program accounts data = ok (.Ok (r,m))) :
    PoolS2_Prefix.run accounts data = ok (.Ok r) ∧
    PoolS2_MasterRead.run decode pda program r.master true = ok (.Ok m) := by
  unfold run at h
  repeat' first
  | (solve | cases h)
  | uncase_result
  | head_reduce h
  | split at h
  all_goals aesop

#print axioms accepted
end AspisR1.PoolS2_MasterStage
end
