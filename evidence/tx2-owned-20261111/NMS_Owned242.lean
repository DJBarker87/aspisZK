import NMS_RowSpec242
import NMS_Fresh
set_option autoImplicit false
noncomputable section
namespace NMS_Owned242
open Aeneas Aeneas.Std Result AdapterRw NMS_OwnedPackets NMS_RowSpec242
variable {Ambient : Type}
abbrev Run (Ambient : Type) (A : Type) := NJU_Log.Run (Event Ambient) A

def authenticate (child : NMS_RowSpec233.Native Ambient) (before : World Ambient)
 (program : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
 (pool : solana_pubkey.Pubkey) (lane : U8) (slot : U64) :
 Run Ambient (core.result.Result Auth PE) :=
 let args : NMS_RowSpec233.Args := ⟨program,accounts,pool,lane,slot⟩
 let outcome := child args before
 ⟨outcome.value,[Event.authenticate args before outcome]⟩

def scan (ops : Ops) (inputs : List Nat) (auth : Auth) (bytes : Slice U8) :
 Run Ambient (core.result.Result Scanned PE) :=
 let reply := mapReply (fun s : r1_pool_adapter.ScannedAsqaProof =>
  Scanned.mk ⟨NMS_Fresh.next (inputs ++ auth.owners),s.candidate_afterstate⟩ s.proof_length)
  (ops.op51 bytes)
 NJU_Log.record (.scan bytes) reply

def reconstruct (ops : Ops) (inputs : List Nat) (request : Request)
 (auth : Auth) (candidate : Box Candidate) : Run Ambient (core.result.Result (Box Statement) PE) :=
 let reply := mapReply (fun statement =>
  Box.mk (NMS_Fresh.next (inputs ++ auth.owners ++ [candidate.owner])) statement)
  (ops.op52 request auth.erase candidate.payload)
 NJU_Log.record (.reconstruct request auth candidate) reply

def G (ops : Ops) (child : NMS_RowSpec233.Native Ambient)
 (before : World Ambient) (inputOwners : List Nat)
  (verifier_program : solana_pubkey.Pubkey)
  (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
  (instruction_data : Slice Std.U8)
  (current_slot : core.result.Result Std.U64 solana_program_error.ProgramError)
  :
  Run Ambient (core.result.Result Validated
    solana_program_error.ProgramError)
  := do
  let i := Slice.len instruction_data
  let i1 ←
    aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES
  if i != i1
  then
    ok (core.result.Result.Err
      solana_program_error.ProgramError.InvalidInstructionData)
  else
    let r ← NJU_Log.record (fun reply => Event.plain (NLM_Validate242.Event.decode instruction_data reply) (by trivial)) (ops.op23 instruction_data)
    let r1 ←
      core.result.Result.map_err
        r1_pool_adapter.owned.validate_asq8.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError
        r ()
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let b ←
        core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
          val.verifier_profile r1_pool_adapter.PROFILE_BINDING
      if b
      then
        ok (core.result.Result.Err
          solana_program_error.ProgramError.InvalidInstructionData)
      else
        let b1 ←
          core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
            val.verifier_release r1_pool_adapter.RELEASE_BINDING
        if b1
        then
          ok (core.result.Result.Err
            solana_program_error.ProgramError.InvalidInstructionData)
        else
          let a ← NJU_Log.record (fun reply => Event.plain (NLM_Validate242.Event.poolId reply) (by trivial)) (ops.op45)
          let b2 ←
            core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
              val.pool_program a
          if b2
          then
            ok (core.result.Result.Err
              solana_program_error.ProgramError.InvalidInstructionData)
          else
            let pool_program ← NJU_Log.record (fun reply => Event.plain (NLM_Validate242.Event.fromBytes val.pool_program reply) (by trivial)) (ops.op37 val.pool_program)
            let a1 ← NJU_Log.record (fun reply => Event.plain (NLM_Validate242.Event.nullifier val.«public» reply) (by trivial)) (ops.op20 val.«public»)
            let r2 ← NJU_Log.record (fun reply => Event.plain (NLM_Validate242.Event.outputLane a1 reply) (by trivial)) (ops.op17 a1)
            let r3 ←
              core.result.Result.map_err
                r1_pool_adapter.owned.validate_asq8.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestAccountErrorV1ProgramError
                r2 ()
            let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r3
            match cf1 with
            | core.ops.control_flow.ControlFlow.Continue val1 =>
              let cf2 ←
                core.result.Result.Insts.CoreOpsTry.branch current_slot
              match cf2 with
              | core.ops.control_flow.ControlFlow.Continue val2 =>
                let r4 ←
                  authenticate child before verifier_program accounts pool_program val1 val2
                let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r4
                match cf3 with
                | core.ops.control_flow.ControlFlow.Continue val3 =>
                  let o ← ops.op9 accounts
                  let r5 ←
                    core.option.Option.ok_or o
                      solana_program_error.ProgramError.NotEnoughAccountKeys
                  let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r5
                  match cf4 with
                  | core.ops.control_flow.ControlFlow.Continue val4 =>
                    let r6 ← NJU_Log.record (fun reply => Event.plain (NLM_Validate242.Event.data val4 reply) (by trivial)) ((r1_pool_adapter.owned.OwnedAccount.data ops) val4)
                    let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r6
                    match cf5 with
                    | core.ops.control_flow.ControlFlow.Continue val5 =>
                      let r7 ← scan ops inputOwners val3 val5
                      let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r7
                      match cf6 with
                      | core.ops.control_flow.ControlFlow.Continue val6 =>
                        let r8 ← reconstruct ops inputOwners val val3 val6.candidate
                        let cf7 ←
                          core.result.Result.Insts.CoreOpsTry.branch r8
                        match cf7 with
                        | core.ops.control_flow.ControlFlow.Continue val7 =>
                          ok (core.result.Result.Ok
                            {
                              statement := val7,
                              proofLength := val6.proofLength
                            })
                        | core.ops.control_flow.ControlFlow.Break residual =>
                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                            Validated
                            (core.convert.FromSame
                            solana_program_error.ProgramError) residual
                      | core.ops.control_flow.ControlFlow.Break residual =>
                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                          Validated (core.convert.FromSame
                          solana_program_error.ProgramError) residual
                    | core.ops.control_flow.ControlFlow.Break residual =>
                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                        Validated (core.convert.FromSame
                        solana_program_error.ProgramError) residual
                  | core.ops.control_flow.ControlFlow.Break residual =>
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                      Validated (core.convert.FromSame
                      solana_program_error.ProgramError) residual
                | core.ops.control_flow.ControlFlow.Break residual =>
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                    Validated (core.convert.FromSame
                    solana_program_error.ProgramError) residual
              | core.ops.control_flow.ControlFlow.Break residual =>
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                  Validated (core.convert.FromSame
                  solana_program_error.ProgramError) residual
            | core.ops.control_flow.ControlFlow.Break residual =>
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                Validated (core.convert.FromSame
                solana_program_error.ProgramError) residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        Validated (core.convert.FromSame
        solana_program_error.ProgramError) residual

def finish (before : World Ambient) (run : Run Ambient (core.result.Result Validated PE)) : Outcome Ambient :=
 match run.result with
 | .ok reply => .returned reply before run.events
 | .fail error => .stopped run.events (.failed error)
 | .div => .stopped run.events .diverged
end NMS_Owned242
