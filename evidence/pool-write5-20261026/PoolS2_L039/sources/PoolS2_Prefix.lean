import PoolS2_Count
import PoolS2_Instruction
import PoolS2_PayerExact
import PoolS2_UniqueRoles
set_option autoImplicit false
noncomputable section
namespace AspisR1.PoolS2_Prefix
open Aeneas Aeneas.Std Result PoolS2_PrefixSource

structure Roles where
  master : Account
  lanes : Slice Account
  checkpoint : Account
  payer : Account
  system : Account

def keys (accounts : Slice Account) : Slice PoolS2_RightStep.Key :=
  ⟨accounts.val.map (fun a => a.key),by simpa using accounts.property⟩

/-- P6 key projection only. Native full-scanner equivalence remains open;
the native original role0/9 leaf has its separate K011 receipt. -/
def unique (accounts : Slice Account) : Result (core.result.Result Unit Error) := do
  let yes ← PoolS2_Unique.unique_keys (keys accounts)
  if !yes then ok (.Err AdapterRw.solana_program_error.ProgramError.InvalidArgument)
  else ok (.Ok ())

def select (accounts : Slice Account) : Result Roles := do
  let master ← Slice.index_usize accounts 0#usize
  let lanes ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Account)
    accounts {start := 1#usize, «end» := 9#usize}
  let checkpoint ← Slice.index_usize accounts 9#usize
  let payer ← Slice.index_usize accounts 10#usize
  let system ← Slice.index_usize accounts 11#usize
  ok ⟨master,lanes,checkpoint,payer,system⟩

/-- Original F2136–2147 source order on canonical owned metadata. Stops BEFORE
the planner. This is not a native AccountInfo caller or allocation/cleanup law. -/
def run (accounts : Slice Account) (data : Slice U8) :
    Result (core.result.Result Roles Error) := do
  let instruction ← PoolS2_InstructionSource.pair_forest.decode_pair_forest_checkpoint_instruction_v1 data
  match instruction with
  | .Err e => ok (.Err e)
  | .Ok _ =>
    let count ← pair_forest.require_exact_account_count accounts 12#usize
    match count with
    | .Err e => ok (.Err e)
    | .Ok _ =>
      let distinct ← unique accounts
      match distinct with
      | .Err e => ok (.Err e)
      | .Ok _ =>
        let roles ← select accounts
        let payer ← processor.require_payer_and_system_program roles.payer roles.system
        match payer with
        | .Err e => ok (.Err e)
        | .Ok _ => ok (.Ok roles)

#print axioms unique
#print axioms select
#print axioms run
end AspisR1.PoolS2_Prefix
end
