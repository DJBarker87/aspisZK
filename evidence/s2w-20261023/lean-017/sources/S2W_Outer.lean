import S2W_Trace
/-! Exact monadic port of the two outer caller bodies. Pure helpers are
atomic Result lifts here. This is not an all-helper/native trace claim. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.S2W_Outer
open Aeneas Aeneas.Std Result AdapterRw S2W_Trace
universe v
structure Effects (M : Type → Type v) where
  op0 : ∀ {T : Type} {U : Type} {N : Std.Usize} (cmpPartialEqInst : core.cmp.PartialEq T U), (Slice T) → (Array U N) → M Bool
  op1 : ∀ {T : Type} {U : Type} {N : Std.Usize} (cmpPartialEqInst : core.cmp.PartialEq T U), (Slice T) → (Array U N) → M Bool
  op2 : ∀ {T : Type} (cmpPartialEqInst : core.cmp.PartialEq T T), (Option T) → (Option T) → M Bool
  op3 : ∀ {T : Type}, core.ops.range.RangeFull → (Slice T) → M ((Slice T) × (Slice T → Slice T))
  op4 : ∀ {T : Type}, core.ops.range.RangeFull → (Slice T) → M (Slice T)
  op5 : ∀ {T : Type}, core.ops.range.RangeFull → (MutRawPtr (Slice T)) → M (MutRawPtr (Slice T))
  op6 : ∀ {T : Type}, core.ops.range.RangeFull → (ConstRawPtr (Slice T)) → M (ConstRawPtr (Slice T))
  op7 : ∀ {T : Type}, core.ops.range.RangeFull → (Slice T) → M ((Option (Slice T)) × (Option (Slice T) → Slice T))
  op8 : ∀ {T : Type}, core.ops.range.RangeFull → (Slice T) → M (Option (Slice T))
  op9 : ∀ {T : Type}, (Slice T) → M (Option T)
  op10 : ∀ {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H), aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public → (Slice Std.U8) → (Slice Std.U8) → Std.Usize → H → (Option (aspis_r1_cost_probe.verifier.Phase → Result Unit)) → M (core.result.Result (alloc.vec.Vec Std.U8) aspis_r1_cost_probe.verifier.Error)
  op11 : ∀ {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H), (Slice Std.U8) → (Slice Std.U8) → (Slice Std.U8) → H → (Option (aspis_r1_cost_probe.verifier.Phase → Result Unit)) → M (core.result.Result Unit aspis_r1_cost_probe.verifier.Error)
  op12 : aspis_r1_cost_probe.transport.Variant → M Std.Usize
  op13 : M Std.U8
  op14 : M Std.U8
  op15 : aspis_statement.pool_v1.format.VerifierPolicyV1 → M (core.result.Result Unit aspis_statement.pool_v1.format.PoolV1FormatError)
  op16 : M Std.U8
  op17 : (Array aspis_core.field.M31 8#usize) → M (core.result.Result Std.U8 aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1)
  op18 : M Std.U8
  op19 : M Std.Usize
  op20 : aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalPaymentV1 → M (Array aspis_core.field.M31 8#usize)
  op21 : aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1 → M (core.result.Result Unit aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
  op22 : aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1 → M (core.result.Result (Array Std.U8 1880#usize) aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
  op23 : (Slice Std.U8) → M (core.result.Result aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalRequestV1 aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
  op24 : aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 → M (core.result.Result (Array Std.U8 688#usize) aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1)
  op25 : aspis_statement.pool_v1.verifier_registry.VerifierRegistryV1 → M Bool
  op26 : aspis_statement.pool_v1.verifier_registry.VerifierRegistryV1 → M Bool
  op27 : aspis_statement.pool_v1.verifier_registry.VerifierRegistryV2 → M Bool
  op28 : aspis_statement.pool_v1.verifier_registry.VerifierRegistryV2 → M Bool
  op29 : aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntryV2 → Std.U64 → M Bool
  op30 : aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntryV1 → Std.U64 → M Bool
  op31 : (Slice Std.U8) → M (core.result.Result aspis_statement.pool_v1.verifier_registry.VerifierRegistryV1 aspis_statement.pool_v1.verifier_registry.PoolV1VerifierRegistryFormatError)
  op32 : (Slice Std.U8) → M (core.result.Result aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntryV1 aspis_statement.pool_v1.verifier_registry.PoolV1VerifierRegistryFormatError)
  op33 : (Slice Std.U8) → M (core.result.Result aspis_statement.pool_v1.verifier_registry.VerifierRegistryV2 aspis_statement.pool_v1.verifier_registry.PoolV1VerifierRegistryFormatError)
  op34 : (Slice Std.U8) → M (core.result.Result aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntryV2 aspis_statement.pool_v1.verifier_registry.PoolV1VerifierRegistryFormatError)
  op35 : solana_program_error.ProgramError → M solana_program_error.ProgramError
  op36 : solana_pubkey.Pubkey → solana_pubkey.Pubkey → M Bool
  op37 : (Array Std.U8 32#usize) → M solana_pubkey.Pubkey
  op38 : (Slice (Slice Std.U8)) → solana_pubkey.Pubkey → M (core.result.Result solana_pubkey.Pubkey solana_pubkey.PubkeyError)
  op39 : solana_pubkey.Pubkey → M (Array Std.U8 32#usize)
  op40 : solana_pubkey.Pubkey → M (Slice Std.U8)
  op41 : M solana_pubkey.Pubkey
  op42 : SolanaDigest → M SolanaDigest
  op43 : SolanaDigest → (Slice (Slice Std.U8)) → M (Array Std.U8 32#usize)
  op44 : aspis_r1_cost_probe.verifier.Error → M solana_program_error.ProgramError
  op45 : M (Array Std.U8 32#usize)
  op46 : M (Array Std.U8 32#usize)
  op47 : (Slice Std.U8) → M (core.result.Result aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1 solana_program_error.ProgramError)
  op48 : (Slice Std.U8) → M (core.result.Result aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1 solana_program_error.ProgramError)
  op49 : (Slice Std.U8) → M (core.result.Result aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestCheckpointV1 solana_program_error.ProgramError)
  op50 : (Slice Std.U8) → M (core.result.Result aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestLaneStateV1 solana_program_error.ProgramError)
  op51 : (Slice Std.U8) → M (core.result.Result r1_pool_adapter.ScannedAsqaProof solana_program_error.ProgramError)
  op52 : aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalRequestV1 → r1_pool_adapter.AuthenticatedAsq8Accounts → aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 → M (core.result.Result aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1 solana_program_error.ProgramError)
  op53 : aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1 → M (core.result.Result Unit solana_program_error.ProgramError)

def sourceEffects (ops : Ops) : Effects Result := {
  op0 := ops.op0
  op1 := ops.op1
  op2 := ops.op2
  op3 := ops.op3
  op4 := ops.op4
  op5 := ops.op5
  op6 := ops.op6
  op7 := ops.op7
  op8 := ops.op8
  op9 := ops.op9
  op10 := ops.op10
  op11 := ops.op11
  op12 := ops.op12
  op13 := ops.op13
  op14 := ops.op14
  op15 := ops.op15
  op16 := ops.op16
  op17 := ops.op17
  op18 := ops.op18
  op19 := ops.op19
  op20 := ops.op20
  op21 := ops.op21
  op22 := ops.op22
  op23 := ops.op23
  op24 := ops.op24
  op25 := ops.op25
  op26 := ops.op26
  op27 := ops.op27
  op28 := ops.op28
  op29 := ops.op29
  op30 := ops.op30
  op31 := ops.op31
  op32 := ops.op32
  op33 := ops.op33
  op34 := ops.op34
  op35 := ops.op35
  op36 := ops.op36
  op37 := ops.op37
  op38 := ops.op38
  op39 := ops.op39
  op40 := ops.op40
  op41 := ops.op41
  op42 := ops.op42
  op43 := ops.op43
  op44 := ops.op44
  op45 := ops.op45
  op46 := ops.op46
  op47 := ops.op47
  op48 := ops.op48
  op49 := ops.op49
  op50 := ops.op50
  op51 := ops.op51
  op52 := ops.op52
  op53 := ops.op53
}

def traceEffects : Effects Code := {
  op0 := fun {T} {U} {N} cmpPartialEqInst a0 a1 => perform (.op0 (T := T) (U := U) (N := N) cmpPartialEqInst a0 a1)
  op1 := fun {T} {U} {N} cmpPartialEqInst a0 a1 => perform (.op1 (T := T) (U := U) (N := N) cmpPartialEqInst a0 a1)
  op2 := fun {T} cmpPartialEqInst a0 a1 => perform (.op2 (T := T) cmpPartialEqInst a0 a1)
  op3 := fun {T} a0 a1 => perform (.op3 (T := T) a0 a1)
  op4 := fun {T} a0 a1 => perform (.op4 (T := T) a0 a1)
  op5 := fun {T} a0 a1 => perform (.op5 (T := T) a0 a1)
  op6 := fun {T} a0 a1 => perform (.op6 (T := T) a0 a1)
  op7 := fun {T} a0 a1 => perform (.op7 (T := T) a0 a1)
  op8 := fun {T} a0 a1 => perform (.op8 (T := T) a0 a1)
  op9 := fun {T} a0 => perform (.op9 (T := T) a0)
  op10 := fun {H} aspis_coredigestDigest32Inst a0 a1 a2 a3 a4 a5 => perform (.op10 (H := H) aspis_coredigestDigest32Inst a0 a1 a2 a3 a4 a5)
  op11 := fun {H} aspis_coredigestDigest32Inst a0 a1 a2 a3 a4 => perform (.op11 (H := H) aspis_coredigestDigest32Inst a0 a1 a2 a3 a4)
  op12 := fun a0 => perform (.op12 a0)
  op13 := perform (.op13 )
  op14 := perform (.op14 )
  op15 := fun a0 => perform (.op15 a0)
  op16 := perform (.op16 )
  op17 := fun a0 => perform (.op17 a0)
  op18 := perform (.op18 )
  op19 := perform (.op19 )
  op20 := fun a0 => perform (.op20 a0)
  op21 := fun a0 => perform (.op21 a0)
  op22 := fun a0 => perform (.op22 a0)
  op23 := fun a0 => perform (.op23 a0)
  op24 := fun a0 => perform (.op24 a0)
  op25 := fun a0 => perform (.op25 a0)
  op26 := fun a0 => perform (.op26 a0)
  op27 := fun a0 => perform (.op27 a0)
  op28 := fun a0 => perform (.op28 a0)
  op29 := fun a0 a1 => perform (.op29 a0 a1)
  op30 := fun a0 a1 => perform (.op30 a0 a1)
  op31 := fun a0 => perform (.op31 a0)
  op32 := fun a0 => perform (.op32 a0)
  op33 := fun a0 => perform (.op33 a0)
  op34 := fun a0 => perform (.op34 a0)
  op35 := fun a0 => perform (.op35 a0)
  op36 := fun a0 a1 => perform (.op36 a0 a1)
  op37 := fun a0 => perform (.op37 a0)
  op38 := fun a0 a1 => perform (.op38 a0 a1)
  op39 := fun a0 => perform (.op39 a0)
  op40 := fun a0 => perform (.op40 a0)
  op41 := perform (.op41 )
  op42 := fun a0 => perform (.op42 a0)
  op43 := fun a0 a1 => perform (.op43 a0 a1)
  op44 := fun a0 => perform (.op44 a0)
  op45 := perform (.op45 )
  op46 := perform (.op46 )
  op47 := fun a0 => perform (.op47 a0)
  op48 := fun a0 => perform (.op48 a0)
  op49 := fun a0 => perform (.op49 a0)
  op50 := fun a0 => perform (.op50 a0)
  op51 := fun a0 => perform (.op51 a0)
  op52 := fun a0 a1 a2 => perform (.op52 a0 a1 a2)
  op53 := fun a0 => perform (.op53 a0)
}
def stage1_owned {M : Type → Type v} [Monad M] [MonadLiftT Result M]
  (ops : Ops) (effects : Effects M)
  (program_id : solana_pubkey.Pubkey)
  (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (data : Slice Std.U8) :
  M (core.result.Result (alloc.vec.Vec Std.U8)
    solana_program_error.ProgramError)
  := do
  let b ←
    effects.op1 core.cmp.PartialEqU8 data
      (Array.make 2#usize [ 3#u8, 10#u8 ])
  if b
  then
    let i := Slice.len accounts
    if i != 3#usize
    then
      pure (core.result.Result.Err
        solana_program_error.ProgramError.InvalidInstructionData)
    else
      let proof_account ← Slice.index_usize accounts 0#usize
      let public_account ← Slice.index_usize accounts 1#usize
      let checkpoint_account ← Slice.index_usize accounts 2#usize
      let r ←
        (r1_pool_adapter.owned.require_distinct_accounts ops)
          (Array.make 3#usize [
            proof_account, public_account, checkpoint_account
            ])
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        let r1 ← r1_pool_adapter.owned.require_readonly_buffer proof_account
        let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
        match cf1 with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          let r2 ←
            r1_pool_adapter.owned.require_readonly_buffer public_account
          let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
          match cf2 with
          | core.ops.control_flow.ControlFlow.Continue _ =>
            let r3 ←
              (r1_pool_adapter.owned.require_verifier_checkpoint ops)
                checkpoint_account program_id true
            let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
            match cf3 with
            | core.ops.control_flow.ControlFlow.Continue _ =>
              let r4 ←
                (r1_pool_adapter.owned.OwnedAccount.data ops) checkpoint_account
              let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r4
              match cf4 with
              | core.ops.control_flow.ControlFlow.Continue val =>
                let r5 ← r1_pool_adapter.owned.require_zero val
                let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r5
                match cf5 with
                | core.ops.control_flow.ControlFlow.Continue _ =>
                  let r6 ←
                    (r1_pool_adapter.owned.OwnedAccount.data ops) public_account
                  let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r6
                  match cf6 with
                  | core.ops.control_flow.ControlFlow.Continue val1 =>
                    let r7 ← effects.op47 val1
                    let cf7 ← core.result.Result.Insts.CoreOpsTry.branch r7
                    match cf7 with
                    | core.ops.control_flow.ControlFlow.Continue val2 =>
                      let r8 ←
                        effects.op21
                          val2
                      let r9 ←
                        core.result.Result.map_err
                          r1_pool_adapter.owned.stage1_owned.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError
                          r8 ()
                      let cf8 ← core.result.Result.Insts.CoreOpsTry.branch r9
                      match cf8 with
                      | core.ops.control_flow.ControlFlow.Continue _ =>
                        let pvpftcv ←
                          aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.common
                            val2
                        let r10 ←
                          effects.op24
                            pvpftcv.lane_transition.candidate_afterstate
                        let r11 ←
                          core.result.Result.map_err
                            r1_pool_adapter.owned.stage1_owned.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1ProgramError
                            r10 ()
                        let cf9 ←
                          core.result.Result.Insts.CoreOpsTry.branch r11
                        match cf9 with
                        | core.ops.control_flow.ControlFlow.Continue val3 =>
                          let r12 ←
                            (r1_pool_adapter.owned.OwnedAccount.data ops)
                              proof_account
                          let cf10 ←
                            core.result.Result.Insts.CoreOpsTry.branch r12
                          match cf10 with
                          | core.ops.control_flow.ControlFlow.Continue val4 =>
                            let proof_length ←
                              aspis_r1_cost_probe.verifier.PROOF_BYTES
                            let proof_start ←
                              (aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES ops)
                            let o ←
                              lift (Usize.checked_add proof_start proof_length)
                            let r13 ←
                              core.option.Option.ok_or o
                                solana_program_error.ProgramError.InvalidAccountData
                            let cf11 ←
                              core.result.Result.Insts.CoreOpsTry.branch r13
                            match cf11 with
                            | core.ops.control_flow.ControlFlow.Continue val5
                              =>
                              let i1 := Slice.len val4
                              if i1 != val5
                              then
                                pure (core.result.Result.Err
                                  solana_program_error.ProgramError.InvalidAccountData)
                              else
                                let s ←
                                  core.slice.index.Slice.index
                                    (core.slice.index.SliceIndexRangeToUsizeSlice
                                    Std.U8) val4 { «end» := proof_start }
                                let b1 ←
                                  effects.op0
                                    core.cmp.PartialEqU8 s val3
                                if b1
                                then
                                  pure (core.result.Result.Err
                                    solana_program_error.ProgramError.InvalidAccountData)
                                else
                                  let i2 ←
                                    lift (Std.Usize.wrapping_add proof_start
                                      8#usize)
                                  let i3 ← Slice.index_usize val4 i2
                                  let i4 ←
                                    aspis_r1_cost_probe.transport.Variant.tag
                                      aspis_r1_cost_probe.transport.Variant.S2
                                  if i3 != i4
                                  then
                                    pure (core.result.Result.Err
                                      solana_program_error.ProgramError.InvalidAccountData)
                                  else
                                    let p ←
                                      aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
                                        val2
                                    let s1 ←
                                      core.slice.index.Slice.index
                                        (core.slice.index.SliceIndexRangeUsizeSlice
                                        Std.U8) val4
                                        { start := proof_start, «end» := val5
                                        }
                                    let i5 ← Slice.index_usize data 1#usize
                                    let i6 ← lift (UScalar.cast .Usize i5)
                                    let r14 ← (first_decoded ops) p val1 s1 i6
                                    let cf12 ←
                                      core.result.Result.Insts.CoreOpsTry.branch
                                        r14
                                    match cf12 with
                                    |
                                      core.ops.control_flow.ControlFlow.Continue
                                      val6 =>
                                      let i7 := alloc.vec.Vec.len val6
                                      let i8 := Slice.len val
                                      if i7 != i8
                                      then
                                        pure (core.result.Result.Err
                                          solana_program_error.ProgramError.InvalidAccountData)
                                      else pure (core.result.Result.Ok val6)
                                    | core.ops.control_flow.ControlFlow.Break
                                      residual =>
                                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                        (alloc.vec.Vec Std.U8)
                                        (core.convert.FromSame
                                        solana_program_error.ProgramError)
                                        residual
                            | core.ops.control_flow.ControlFlow.Break residual
                              =>
                              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                (alloc.vec.Vec Std.U8) (core.convert.FromSame
                                solana_program_error.ProgramError) residual
                          | core.ops.control_flow.ControlFlow.Break residual =>
                            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                              (alloc.vec.Vec Std.U8) (core.convert.FromSame
                              solana_program_error.ProgramError) residual
                        | core.ops.control_flow.ControlFlow.Break residual =>
                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                            (alloc.vec.Vec Std.U8) (core.convert.FromSame
                            solana_program_error.ProgramError) residual
                      | core.ops.control_flow.ControlFlow.Break residual =>
                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                          (alloc.vec.Vec Std.U8) (core.convert.FromSame
                          solana_program_error.ProgramError) residual
                    | core.ops.control_flow.ControlFlow.Break residual =>
                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                        (alloc.vec.Vec Std.U8) (core.convert.FromSame
                        solana_program_error.ProgramError) residual
                  | core.ops.control_flow.ControlFlow.Break residual =>
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                      (alloc.vec.Vec Std.U8) (core.convert.FromSame
                      solana_program_error.ProgramError) residual
                | core.ops.control_flow.ControlFlow.Break residual =>
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                    (alloc.vec.Vec Std.U8) (core.convert.FromSame
                    solana_program_error.ProgramError) residual
              | core.ops.control_flow.ControlFlow.Break residual =>
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                  (alloc.vec.Vec Std.U8) (core.convert.FromSame
                  solana_program_error.ProgramError) residual
            | core.ops.control_flow.ControlFlow.Break residual =>
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                (alloc.vec.Vec Std.U8) (core.convert.FromSame
                solana_program_error.ProgramError) residual
          | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              (alloc.vec.Vec Std.U8) (core.convert.FromSame
              solana_program_error.ProgramError) residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            (alloc.vec.Vec Std.U8) (core.convert.FromSame
            solana_program_error.ProgramError) residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (alloc.vec.Vec Std.U8) (core.convert.FromSame
          solana_program_error.ProgramError) residual
  else
    let b1 ←
      effects.op1 core.cmp.PartialEqU8 data
        (Array.make 2#usize [ 3#u8, 11#u8 ])
    if b1
    then
      let i := Slice.len accounts
      if i != 3#usize
      then
        pure (core.result.Result.Err
          solana_program_error.ProgramError.InvalidInstructionData)
      else
        let proof_account ← Slice.index_usize accounts 0#usize
        let public_account ← Slice.index_usize accounts 1#usize
        let checkpoint_account ← Slice.index_usize accounts 2#usize
        let r ←
          (r1_pool_adapter.owned.require_distinct_accounts ops)
            (Array.make 3#usize [
              proof_account, public_account, checkpoint_account
              ])
        let cf ← core.result.Result.Insts.CoreOpsTry.branch r
        match cf with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          let r1 ←
            r1_pool_adapter.owned.require_readonly_buffer proof_account
          let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
          match cf1 with
          | core.ops.control_flow.ControlFlow.Continue _ =>
            let r2 ←
              r1_pool_adapter.owned.require_readonly_buffer public_account
            let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
            match cf2 with
            | core.ops.control_flow.ControlFlow.Continue _ =>
              let r3 ←
                (r1_pool_adapter.owned.require_verifier_checkpoint ops)
                  checkpoint_account program_id true
              let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
              match cf3 with
              | core.ops.control_flow.ControlFlow.Continue _ =>
                let r4 ←
                  (r1_pool_adapter.owned.OwnedAccount.data ops) checkpoint_account
                let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r4
                match cf4 with
                | core.ops.control_flow.ControlFlow.Continue val =>
                  let r5 ← r1_pool_adapter.owned.require_zero val
                  let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r5
                  match cf5 with
                  | core.ops.control_flow.ControlFlow.Continue _ =>
                    let r6 ←
                      (r1_pool_adapter.owned.OwnedAccount.data ops) public_account
                    let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r6
                    match cf6 with
                    | core.ops.control_flow.ControlFlow.Continue val1 =>
                      let r7 ←
                        effects.op47 val1
                      let cf7 ← core.result.Result.Insts.CoreOpsTry.branch r7
                      match cf7 with
                      | core.ops.control_flow.ControlFlow.Continue val2 =>
                        let r8 ←
                          effects.op21
                            val2
                        let r9 ←
                          core.result.Result.map_err
                            r1_pool_adapter.owned.stage1_owned.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError
                            r8 ()
                        let cf8 ←
                          core.result.Result.Insts.CoreOpsTry.branch r9
                        match cf8 with
                        | core.ops.control_flow.ControlFlow.Continue _ =>
                          let pvpftcv ←
                            aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.common
                              val2
                          let r10 ←
                            effects.op24
                              pvpftcv.lane_transition.candidate_afterstate
                          let r11 ←
                            core.result.Result.map_err
                              r1_pool_adapter.owned.stage1_owned.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1ProgramError
                              r10 ()
                          let cf9 ←
                            core.result.Result.Insts.CoreOpsTry.branch r11
                          match cf9 with
                          | core.ops.control_flow.ControlFlow.Continue val3 =>
                            let r12 ←
                              (r1_pool_adapter.owned.OwnedAccount.data ops)
                                proof_account
                            let cf10 ←
                              core.result.Result.Insts.CoreOpsTry.branch r12
                            match cf10 with
                            | core.ops.control_flow.ControlFlow.Continue val4
                              =>
                              let proof_length ←
                                aspis_r1_cost_probe.verifier.PROOF_BYTES
                              let proof_start ←
                                (aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES ops)
                              let o ←
                                lift (Usize.checked_add proof_start
                                  proof_length)
                              let r13 ←
                                core.option.Option.ok_or o
                                  solana_program_error.ProgramError.InvalidAccountData
                              let cf11 ←
                                core.result.Result.Insts.CoreOpsTry.branch r13
                              match cf11 with
                              | core.ops.control_flow.ControlFlow.Continue val5
                                =>
                                let i1 := Slice.len val4
                                if i1 != val5
                                then
                                  pure (core.result.Result.Err
                                    solana_program_error.ProgramError.InvalidAccountData)
                                else
                                  let s ←
                                    core.slice.index.Slice.index
                                      (core.slice.index.SliceIndexRangeToUsizeSlice
                                      Std.U8) val4 { «end» := proof_start }
                                  let b2 ←
                                    effects.op0
                                      core.cmp.PartialEqU8 s val3
                                  if b2
                                  then
                                    pure (core.result.Result.Err
                                      solana_program_error.ProgramError.InvalidAccountData)
                                  else
                                    let i2 ←
                                      lift (Std.Usize.wrapping_add proof_start
                                        8#usize)
                                    let i3 ← Slice.index_usize val4 i2
                                    let i4 ←
                                      aspis_r1_cost_probe.transport.Variant.tag
                                        aspis_r1_cost_probe.transport.Variant.S2
                                    if i3 != i4
                                    then
                                      pure (core.result.Result.Err
                                        solana_program_error.ProgramError.InvalidAccountData)
                                    else
                                      let p ←
                                        aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
                                          val2
                                      let s1 ←
                                        core.slice.index.Slice.index
                                          (core.slice.index.SliceIndexRangeUsizeSlice
                                          Std.U8) val4
                                          {
                                            start := proof_start,
                                            «end» := val5
                                          }
                                      let i5 ← Slice.index_usize data 1#usize
                                      let i6 ← lift (UScalar.cast .Usize i5)
                                      let r14 ← (first_decoded ops) p val1 s1 i6
                                      let cf12 ←
                                        core.result.Result.Insts.CoreOpsTry.branch
                                          r14
                                      match cf12 with
                                      |
                                        core.ops.control_flow.ControlFlow.Continue
                                        val6 =>
                                        let i7 := alloc.vec.Vec.len val6
                                        let i8 := Slice.len val
                                        if i7 != i8
                                        then
                                          pure (core.result.Result.Err
                                            solana_program_error.ProgramError.InvalidAccountData)
                                        else pure (core.result.Result.Ok val6)
                                      | core.ops.control_flow.ControlFlow.Break
                                        residual =>
                                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                          (alloc.vec.Vec Std.U8)
                                          (core.convert.FromSame
                                          solana_program_error.ProgramError)
                                          residual
                              | core.ops.control_flow.ControlFlow.Break
                                residual =>
                                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                  (alloc.vec.Vec Std.U8) (core.convert.FromSame
                                  solana_program_error.ProgramError) residual
                            | core.ops.control_flow.ControlFlow.Break residual
                              =>
                              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                (alloc.vec.Vec Std.U8) (core.convert.FromSame
                                solana_program_error.ProgramError) residual
                          | core.ops.control_flow.ControlFlow.Break residual =>
                            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                              (alloc.vec.Vec Std.U8) (core.convert.FromSame
                              solana_program_error.ProgramError) residual
                        | core.ops.control_flow.ControlFlow.Break residual =>
                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                            (alloc.vec.Vec Std.U8) (core.convert.FromSame
                            solana_program_error.ProgramError) residual
                      | core.ops.control_flow.ControlFlow.Break residual =>
                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                          (alloc.vec.Vec Std.U8) (core.convert.FromSame
                          solana_program_error.ProgramError) residual
                    | core.ops.control_flow.ControlFlow.Break residual =>
                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                        (alloc.vec.Vec Std.U8) (core.convert.FromSame
                        solana_program_error.ProgramError) residual
                  | core.ops.control_flow.ControlFlow.Break residual =>
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                      (alloc.vec.Vec Std.U8) (core.convert.FromSame
                      solana_program_error.ProgramError) residual
                | core.ops.control_flow.ControlFlow.Break residual =>
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                    (alloc.vec.Vec Std.U8) (core.convert.FromSame
                    solana_program_error.ProgramError) residual
              | core.ops.control_flow.ControlFlow.Break residual =>
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                  (alloc.vec.Vec Std.U8) (core.convert.FromSame
                  solana_program_error.ProgramError) residual
            | core.ops.control_flow.ControlFlow.Break residual =>
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                (alloc.vec.Vec Std.U8) (core.convert.FromSame
                solana_program_error.ProgramError) residual
          | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              (alloc.vec.Vec Std.U8) (core.convert.FromSame
              solana_program_error.ProgramError) residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            (alloc.vec.Vec Std.U8) (core.convert.FromSame
            solana_program_error.ProgramError) residual
    else
      pure (core.result.Result.Err
        solana_program_error.ProgramError.InvalidInstructionData)

def stage2_owned {M : Type → Type v} [Monad M] [MonadLiftT Result M]
  (ops : Ops) (effects : Effects M)
  (program_id : solana_pubkey.Pubkey)
  (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (data : Slice Std.U8)
  (current_slot : core.result.Result Std.U64 solana_program_error.ProgramError)
  :
  M (core.result.Result Unit solana_program_error.ProgramError)
  := do
  let i := Slice.len accounts
  if i != 7#usize
  then
    pure (core.result.Result.Err
      solana_program_error.ProgramError.InvalidInstructionData)
  else
    let o ←
      core.slice.Slice.get (core.slice.index.SliceIndexRangeToUsizeSlice
        Std.U8) data { «end» := 4#usize }
    let s ←
      core.array.Array.index (core.ops.index.IndexSlice
        ((core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice ops)
        Std.U8))
        aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_MAGIC
        ()
    let b ←
      core.cmp.PartialEq.ne.trait_default
        ((core.option.Option.Insts.CoreCmpPartialEqOption ops)
        (core.cmp.PartialEqShared (Slice.Insts.CoreCmpPartialEqSlice
        core.cmp.PartialEqU8))) o (some s)
    if b
    then
      pure (core.result.Result.Err
        solana_program_error.ProgramError.InvalidInstructionData)
    else
      let r ←
        (r1_pool_adapter.owned.validate_asq8 ops) program_id accounts data
          current_slot
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue val =>
        let oa ← Slice.index_usize accounts 0#usize
        let r1 ← (r1_pool_adapter.owned.OwnedAccount.data ops) oa
        let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
        match cf1 with
        | core.ops.control_flow.ControlFlow.Continue val1 =>
          let oa1 ← Slice.index_usize accounts 6#usize
          let r2 ← (r1_pool_adapter.owned.OwnedAccount.data ops) oa1
          let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
          match cf2 with
          | core.ops.control_flow.ControlFlow.Continue val2 =>
            let proof_start ←
              (aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES ops)
            let o1 ← lift (Usize.checked_add proof_start val.proof_length)
            let r3 ←
              core.option.Option.ok_or o1
                solana_program_error.ProgramError.InvalidAccountData
            let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
            match cf3 with
            | core.ops.control_flow.ControlFlow.Continue val3 =>
              let i1 := Slice.len val1
              if i1 != val3
              then
                pure (core.result.Result.Err
                  solana_program_error.ProgramError.InvalidAccountData)
              else
                let r4 ←
                  effects.op22
                    val.statement
                let r5 ←
                  core.result.Result.map_err
                    r1_pool_adapter.owned.stage2_owned.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError
                    r4 ()
                let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r5
                match cf4 with
                | core.ops.control_flow.ControlFlow.Continue val4 =>
                  let s1 ← lift (Array.to_slice val4)
                  let i2 := Slice.len s1
                  let i3 ←
                    (aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES ops)
                  if i2 != i3
                  then
                    pure (core.result.Result.Err
                      solana_program_error.ProgramError.InvalidInstructionData)
                  else
                    let s2 ← lift (Array.to_slice val4)
                    let s3 ←
                      core.slice.index.Slice.index
                        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)
                        val1 { start := proof_start, «end» := val3 }
                    let o2 ← (observer ops)
                    let r6 ←
                      effects.op11
                        (SolanaDigest.Insts.Aspis_coreDigestDigest32 ops) s2 s3 val2
                        () o2
                    let r7 ←
                      core.result.Result.map_err (BuiltinFnOnce
                        aspis_r1_cost_probe.verifier.Error
                        solana_program_error.ProgramError) r6 (ops.op44)
                    let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r7
                    match cf5 with
                    | core.ops.control_flow.ControlFlow.Continue _ =>
                      effects.op53 val.statement
                    | core.ops.control_flow.ControlFlow.Break residual =>
                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                        Unit (core.convert.FromSame
                        solana_program_error.ProgramError) residual
                | core.ops.control_flow.ControlFlow.Break residual =>
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                    Unit (core.convert.FromSame
                    solana_program_error.ProgramError) residual
            | core.ops.control_flow.ControlFlow.Break residual =>
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                Unit (core.convert.FromSame solana_program_error.ProgramError)
                residual
          | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              Unit (core.convert.FromSame solana_program_error.ProgramError)
              residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            Unit (core.convert.FromSame solana_program_error.ProgramError)
            residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          Unit (core.convert.FromSame solana_program_error.ProgramError)
          residual

theorem stage1_source (ops : Ops) (program_id : solana_pubkey.Pubkey)
    (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (data : Slice U8) :
    stage1_owned ops (sourceEffects ops) program_id accounts data =
      r1_pool_adapter.owned.stage1_owned ops program_id accounts data := by rfl

theorem stage2_source (ops : Ops) (program_id : solana_pubkey.Pubkey)
    (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (data : Slice U8)
    (slot : core.result.Result U64 solana_program_error.ProgramError) :
    stage2_owned ops (sourceEffects ops) program_id accounts data slot =
      r1_pool_adapter.owned.stage2_owned ops program_id accounts data slot := by rfl

#print axioms stage1_source
#print axioms stage2_source
end AspisR1.S2W_Outer
