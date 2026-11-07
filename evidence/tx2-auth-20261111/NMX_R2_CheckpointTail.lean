import NMX_LengthCloneCut
set_option autoImplicit false
namespace NMX_R2_CheckpointTail
open Aeneas Aeneas.Std Result AdapterRw
abbrev PE := solana_program_error.ProgramError

def tail (n : Usize) : core.result.Result Unit PE :=
 if n != 1768#usize then .Err .InvalidAccountData else .Ok ()

def after (r : Result (core.result.Result Usize PE)) : Result (core.result.Result Unit PE) := do
 let reply ← r
 match reply with
 | .Err e => ok (.Err e)
 | .Ok n => ok (tail n)

def original (r : Result (core.result.Result Usize PE)) : Result (core.result.Result Unit PE) := do
 let reply ← r
 let cf ← core.result.Result.Insts.CoreOpsTry.branch reply
 match cf with
 | core.ops.control_flow.ControlFlow.Continue n =>
   if n != 1768#usize then ok (.Err .InvalidAccountData) else ok (.Ok ())
 | core.ops.control_flow.ControlFlow.Break residual =>
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
    Unit (core.convert.FromSame PE) residual

/-- One emitted question-mark occurrence, including all fail/div/error arms. -/
theorem fold (r : Result (core.result.Result Usize PE)) : original r = after r := by
 cases r with
 | fail e => rfl
 | div => rfl
 | ok reply =>
   cases reply with
   | Err e => rfl
   | Ok n =>
     cases flag : (n != 1768#usize) <;>
      simp only [original,after,tail,core.result.Result.Insts.CoreOpsTry.branch,
       bind_tc_ok,flag,Bool.false_eq_true,↓reduceIte]
#print axioms fold
end NMX_R2_CheckpointTail
