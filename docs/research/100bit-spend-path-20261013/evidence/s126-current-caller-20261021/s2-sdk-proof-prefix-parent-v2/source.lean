-- Exact fission of both installed source prefix comparisons, full SDK retained.
import S2SdkProofComparatorV1
import S2SdkSnapshotEquivalenceV1
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisS2OwnedStage1.SdkReference.ProofPrefixParent

def stdCmp (bytes : Slice U8) (candidate : Array U8 688#usize) : Result Bool :=
  SourceInstallation.stdSliceArrayNe core.cmp.PartialEqU8 bytes candidate

def loopCmp (bytes : Slice U8) (candidate : Array U8 688#usize) : Result Bool :=
  ProofGate.scalarNe bytes (Array.to_slice candidate)

theorem cmp_eq : loopCmp=stdCmp := by
  funext bytes candidate
  exact ProofGate.scalarNe_eq_standard bytes (Array.to_slice candidate)

def bodyWithPrefixCmp (prefixCmp : Slice U8 → Array U8 688#usize → Result Bool) (ops : Ops)
  (program_id : Array Std.U8 32#usize) (sdk : OwnedSdk) (data : Slice Std.U8)
  (guards : LiveGuards) :
  Result ((core.result.Result Unit solana_program_error.ProgramError) ×
    OwnedSdk × LiveGuards)
  := do
  let b ←
    ops.op1 core.cmp.PartialEqU8 data
      (Array.make 2#usize [ 3#u8, 10#u8 ])
  if b
  then
    let i := alloc.vec.Vec.len sdk.accounts
    if i != 3#usize
    then
      ok (core.result.Result.Err
        solana_program_error.ProgramError.InvalidInstructionData, sdk, guards)
    else
      let proof ←
        alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
          OwnedAccount) sdk.accounts 0#usize
      let public1 ←
        alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
          OwnedAccount) sdk.accounts 1#usize
      let checkpoint ←
        alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
          OwnedAccount) sdk.accounts 2#usize
      let b1 ←
        core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 proof.key
          public1.key
      if b1
      then
        ok (core.result.Result.Err
          solana_program_error.ProgramError.InvalidArgument, sdk, guards)
      else
        let b2 ←
          core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 
            proof.key checkpoint.key
        if b2
        then
          ok (core.result.Result.Err
            solana_program_error.ProgramError.InvalidArgument, sdk, guards)
        else
          let b3 ←
            core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8
              public1.key checkpoint.key
          if b3
          then
            ok (core.result.Result.Err
              solana_program_error.ProgramError.InvalidArgument, sdk, guards)
          else
            if proof.is_signer
            then
              ok (core.result.Result.Err
                solana_program_error.ProgramError.InvalidAccountData, sdk,
                guards)
            else
              if proof.is_writable
              then
                ok (core.result.Result.Err
                  solana_program_error.ProgramError.InvalidAccountData, sdk,
                  guards)
              else
                if proof.executable
                then
                  ok (core.result.Result.Err
                    solana_program_error.ProgramError.InvalidAccountData, sdk,
                    guards)
                else
                  if public1.is_signer
                  then
                    ok (core.result.Result.Err
                      solana_program_error.ProgramError.InvalidAccountData,
                      sdk, guards)
                  else
                    if public1.is_writable
                    then
                      ok (core.result.Result.Err
                        solana_program_error.ProgramError.InvalidAccountData,
                        sdk, guards)
                    else
                      if public1.executable
                      then
                        ok (core.result.Result.Err
                          solana_program_error.ProgramError.InvalidAccountData,
                          sdk, guards)
                      else
                        let b4 ←
                          core.array.equality.PartialEqArray.ne
                            core.cmp.PartialEqU8 checkpoint.owner program_id
                        if b4
                        then
                          ok (core.result.Result.Err
                            solana_program_error.ProgramError.InvalidAccountData,
                            sdk, guards)
                        else
                          if checkpoint.is_signer
                          then
                            ok (core.result.Result.Err
                              solana_program_error.ProgramError.InvalidAccountData,
                              sdk, guards)
                          else
                            if checkpoint.executable
                            then
                              ok (core.result.Result.Err
                                solana_program_error.ProgramError.InvalidAccountData,
                                sdk, guards)
                            else
                              if checkpoint.is_writable
                              then
                                let r ←
                                  owned_data_len sdk checkpoint.data_slot
                                let cf ←
                                  core.result.Result.Insts.CoreOpsTry.branch r
                                match cf with
                                | core.ops.control_flow.ControlFlow.Continue
                                  val =>
                                  let i1 ←
                                    aspis_r1_cost_probe.verifier.checkpoint_size
                                      aspis_r1_cost_probe.transport.Variant.S2
                                  if val != i1
                                  then
                                    ok (core.result.Result.Err
                                      solana_program_error.ProgramError.InvalidAccountData,
                                      sdk, guards)
                                  else
                                    let (r1, sdk1, guards1) ←
                                      owned_acquire_checkpoint sdk guards
                                        checkpoint.data_slot
                                    let cf1 ←
                                      core.result.Result.Insts.CoreOpsTry.branch
                                        r1
                                    match cf1 with
                                    |
                                      core.ops.control_flow.ControlFlow.Continue
                                      _ =>
                                      let odc ←
                                        alloc.vec.Vec.index
                                          (core.slice.index.SliceIndexUsizeSlice
                                          OwnedDataCell) sdk1.data_cells
                                          checkpoint.data_slot
                                      let v ←
                                        alloc.vec.CloneVec.clone
                                          core.clone.CloneU8 odc.bytes
                                      let b5 ← owned_checkpoint_nonzero v
                                      if b5
                                      then
                                        ok (core.result.Result.Err
                                          solana_program_error.ProgramError.AccountAlreadyInitialized,
                                          sdk1, guards1)
                                      else
                                        let (r2, sdk2) ←
                                          owned_acquire_shared sdk1
                                            public1.data_slot
                                        let cf2 ←
                                          core.result.Result.Insts.CoreOpsTry.branch
                                            r2
                                        match cf2 with
                                        |
                                          core.ops.control_flow.ControlFlow.Continue
                                          _ =>
                                          let odc1 ←
                                            alloc.vec.Vec.index
                                              (core.slice.index.SliceIndexUsizeSlice
                                              OwnedDataCell) sdk2.data_cells
                                              public1.data_slot
                                          let public_data ←
                                            alloc.vec.CloneVec.clone
                                              core.clone.CloneU8 odc1.bytes
                                          let s :=
                                            alloc.vec.Vec.deref public_data
                                          let r3 ←
                                            (decode_public_statement_box ops) s
                                          let cf3 ←
                                            core.result.Result.Insts.CoreOpsTry.branch
                                              r3
                                          match cf3 with
                                          |
                                            core.ops.control_flow.ControlFlow.Continue
                                            val1 =>
                                            let r4 ←
                                              ops.op5
                                                val1
                                            let r5 ←
                                              core.result.Result.map_err
                                                owned_stage1_body.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError
                                                r4 ()
                                            let cf4 ←
                                              core.result.Result.Insts.CoreOpsTry.branch
                                                r5
                                            match cf4 with
                                            |
                                              core.ops.control_flow.ControlFlow.Continue
                                              _ =>
                                              let pvpftcv ←
                                                aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.common
                                                  val1
                                              let r6 ←
                                                ops.op8
                                                  pvpftcv.lane_transition.candidate_afterstate
                                              let r7 ←
                                                core.result.Result.map_err
                                                  owned_stage1_body.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1ProgramError
                                                  r6 ()
                                              let cf5 ←
                                                core.result.Result.Insts.CoreOpsTry.branch
                                                  r7
                                              match cf5 with
                                              |
                                                core.ops.control_flow.ControlFlow.Continue
                                                val2 =>
                                                let (r8, sdk3) ←
                                                  owned_acquire_shared sdk2
                                                    proof.data_slot
                                                let cf6 ←
                                                  core.result.Result.Insts.CoreOpsTry.branch
                                                    r8
                                                match cf6 with
                                                |
                                                  core.ops.control_flow.ControlFlow.Continue
                                                  _ =>
                                                  let odc2 ←
                                                    alloc.vec.Vec.index
                                                      (core.slice.index.SliceIndexUsizeSlice
                                                      OwnedDataCell)
                                                      sdk3.data_cells
                                                      proof.data_slot
                                                  let proof_data ←
                                                    alloc.vec.CloneVec.clone
                                                      core.clone.CloneU8
                                                      odc2.bytes
                                                  let proof_length ←
                                                    ops.op4
                                                  let proof_start ←
                                                    ops.op7
                                                  let o ←
                                                    lift (Usize.checked_add
                                                      proof_start proof_length)
                                                  let r9 ←
                                                    ops.op2 o
                                                      solana_program_error.ProgramError.InvalidAccountData
                                                  let cf7 ←
                                                    core.result.Result.Insts.CoreOpsTry.branch
                                                      r9
                                                  match cf7 with
                                                  |
                                                    core.ops.control_flow.ControlFlow.Continue
                                                    val3 =>
                                                    let i2 :=
                                                      alloc.vec.Vec.len
                                                        proof_data
                                                    if i2 != val3
                                                    then
                                                      ok
                                                        (core.result.Result.Err
                                                        solana_program_error.ProgramError.InvalidAccountData,
                                                        sdk3,
                                                        {
                                                          guards1
                                                            with
                                                            «public» :=
                                                              (some
                                                                public1.data_slot),
                                                            proof :=
                                                              (some
                                                                proof.data_slot)
                                                        })
                                                    else
                                                      let s1 ←
                                                        alloc.vec.Vec.index
                                                          (core.slice.index.SliceIndexRangeToUsizeSlice
                                                          Std.U8) proof_data
                                                          {
                                                            «end» :=
                                                              proof_start
                                                          }
                                                      let b6 ←
                                                        prefixCmp s1 val2
                                                      if b6
                                                      then
                                                        ok
                                                          (core.result.Result.Err
                                                          solana_program_error.ProgramError.InvalidAccountData,
                                                          sdk3,
                                                          {
                                                            guards1
                                                              with
                                                              «public» :=
                                                                (some
                                                                  public1.data_slot),
                                                              proof :=
                                                                (some
                                                                  proof.data_slot)
                                                          })
                                                      else
                                                        let i3 ←
                                                          proof_start + 8#usize
                                                        let i4 ←
                                                          alloc.vec.Vec.index
                                                            (core.slice.index.SliceIndexUsizeSlice
                                                            Std.U8) proof_data
                                                            i3
                                                        let i5 ←
                                                          aspis_r1_cost_probe.transport.Variant.tag
                                                            aspis_r1_cost_probe.transport.Variant.S2
                                                        if i4 != i5
                                                        then
                                                          ok
                                                            (core.result.Result.Err
                                                            solana_program_error.ProgramError.InvalidAccountData,
                                                            sdk3,
                                                            {
                                                              guards1
                                                                with
                                                                «public» :=
                                                                  (some
                                                                    public1.data_slot),
                                                                proof :=
                                                                  (some
                                                                    proof.data_slot)
                                                            })
                                                        else
                                                          let p ←
                                                            aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
                                                              val1
                                                          let s2 :=
                                                            alloc.vec.Vec.deref
                                                              public_data
                                                          let s3 ←
                                                            alloc.vec.Vec.index
                                                              (core.slice.index.SliceIndexRangeUsizeSlice
                                                              Std.U8)
                                                              proof_data
                                                              {
                                                                start :=
                                                                  proof_start,
                                                                «end» := val3
                                                              }
                                                          let i6 ←
                                                            Slice.index_usize
                                                              data 1#usize
                                                          let i7 ←
                                                            lift (UScalar.cast
                                                              .Usize i6)
                                                          let r10 ←
                                                            (first_decoded ops) p s2
                                                              s3 i7
                                                          let cf8 ←
                                                            core.result.Result.Insts.CoreOpsTry.branch
                                                              r10
                                                          match cf8 with
                                                          |
                                                            core.ops.control_flow.ControlFlow.Continue
                                                            val4 =>
                                                            let i8 :=
                                                              alloc.vec.Vec.len
                                                                val4
                                                            let odc3 ←
                                                              alloc.vec.Vec.index
                                                                (core.slice.index.SliceIndexUsizeSlice
                                                                OwnedDataCell)
                                                                sdk3.data_cells
                                                                checkpoint.data_slot
                                                            let i9 :=
                                                              alloc.vec.Vec.len
                                                                odc3.bytes
                                                            if i8 != i9
                                                            then
                                                              ok
                                                                (core.result.Result.Err
                                                                solana_program_error.ProgramError.InvalidAccountData,
                                                                sdk3,
                                                                {
                                                                  guards1
                                                                    with
                                                                    «public» :=
                                                                    (some
                                                                    public1.data_slot),
                                                                    proof :=
                                                                    (some
                                                                    proof.data_slot)
                                                                })
                                                            else
                                                              let (odc4,
                                                                index_mut_back)
                                                                ←
                                                                alloc.vec.Vec.index_mut
                                                                  (core.slice.index.SliceIndexUsizeSlice
                                                                  OwnedDataCell)
                                                                  sdk3.data_cells
                                                                  checkpoint.data_slot
                                                              let v1 :=
                                                                index_mut_back
                                                                  {
                                                                    odc4
                                                                    with
                                                                    bytes :=
                                                                    val4
                                                                  }
                                                              ok
                                                                (core.result.Result.Ok
                                                                (),
                                                                {
                                                                  sdk3
                                                                    with
                                                                    data_cells :=
                                                                    v1
                                                                },
                                                                {
                                                                  guards1
                                                                    with
                                                                    «public» :=
                                                                    (some
                                                                    public1.data_slot),
                                                                    proof :=
                                                                    (some
                                                                    proof.data_slot)
                                                                })
                                                          |
                                                            core.ops.control_flow.ControlFlow.Break
                                                            residual =>
                                                            let r11 ←
                                                              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                                Unit
                                                                (core.convert.FromSame
                                                                solana_program_error.ProgramError)
                                                                residual
                                                            ok (r11, sdk3,
                                                              {
                                                                guards1
                                                                  with
                                                                  «public» :=
                                                                    (some
                                                                    public1.data_slot),
                                                                  proof :=
                                                                    (some
                                                                    proof.data_slot)
                                                              })
                                                  |
                                                    core.ops.control_flow.ControlFlow.Break
                                                    residual =>
                                                    let r10 ←
                                                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                        Unit
                                                        (core.convert.FromSame
                                                        solana_program_error.ProgramError)
                                                        residual
                                                    ok (r10, sdk3,
                                                      {
                                                        guards1
                                                          with
                                                          «public» :=
                                                            (some
                                                              public1.data_slot),
                                                          proof :=
                                                            (some
                                                              proof.data_slot)
                                                      })
                                                |
                                                  core.ops.control_flow.ControlFlow.Break
                                                  residual =>
                                                  let r9 ←
                                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                      Unit
                                                      (core.convert.FromSame
                                                      solana_program_error.ProgramError)
                                                      residual
                                                  ok (r9, sdk3,
                                                    {
                                                      guards1
                                                        with
                                                        «public» :=
                                                          (some
                                                            public1.data_slot)
                                                    })
                                              |
                                                core.ops.control_flow.ControlFlow.Break
                                                residual =>
                                                let r8 ←
                                                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                    Unit (core.convert.FromSame
                                                    solana_program_error.ProgramError)
                                                    residual
                                                ok (r8, sdk2,
                                                  {
                                                    guards1
                                                      with
                                                      «public» :=
                                                        (some
                                                          public1.data_slot)
                                                  })
                                            |
                                              core.ops.control_flow.ControlFlow.Break
                                              residual =>
                                              let r6 ←
                                                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                  Unit (core.convert.FromSame
                                                  solana_program_error.ProgramError)
                                                  residual
                                              ok (r6, sdk2,
                                                {
                                                  guards1
                                                    with
                                                    «public» :=
                                                      (some public1.data_slot)
                                                })
                                          |
                                            core.ops.control_flow.ControlFlow.Break
                                            residual =>
                                            let r4 ←
                                              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                Unit (core.convert.FromSame
                                                solana_program_error.ProgramError)
                                                residual
                                            ok (r4, sdk2,
                                              {
                                                guards1
                                                  with
                                                  «public» :=
                                                    (some public1.data_slot)
                                              })
                                        |
                                          core.ops.control_flow.ControlFlow.Break
                                          residual =>
                                          let r3 ←
                                            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                              Unit (core.convert.FromSame
                                              solana_program_error.ProgramError)
                                              residual
                                          ok (r3, sdk2, guards1)
                                    | core.ops.control_flow.ControlFlow.Break
                                      residual =>
                                      let r2 ←
                                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                          Unit (core.convert.FromSame
                                          solana_program_error.ProgramError)
                                          residual
                                      ok (r2, sdk1, guards1)
                                | core.ops.control_flow.ControlFlow.Break
                                  residual =>
                                  let r1 ←
                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                      Unit (core.convert.FromSame
                                      solana_program_error.ProgramError)
                                      residual
                                  ok (r1, sdk, guards)
                              else
                                ok (core.result.Result.Err
                                  solana_program_error.ProgramError.InvalidAccountData,
                                  sdk, guards)
  else
    let b1 ←
      ops.op1 core.cmp.PartialEqU8 data
        (Array.make 2#usize [ 3#u8, 11#u8 ])
    if b1
    then
      let i := alloc.vec.Vec.len sdk.accounts
      if i != 3#usize
      then
        ok (core.result.Result.Err
          solana_program_error.ProgramError.InvalidInstructionData, sdk,
          guards)
      else
        let proof ←
          alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
            OwnedAccount) sdk.accounts 0#usize
        let public1 ←
          alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
            OwnedAccount) sdk.accounts 1#usize
        let checkpoint ←
          alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
            OwnedAccount) sdk.accounts 2#usize
        let b2 ←
          core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 
            proof.key public1.key
        if b2
        then
          ok (core.result.Result.Err
            solana_program_error.ProgramError.InvalidArgument, sdk, guards)
        else
          let b3 ←
            core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8
              proof.key checkpoint.key
          if b3
          then
            ok (core.result.Result.Err
              solana_program_error.ProgramError.InvalidArgument, sdk, guards)
          else
            let b4 ←
              core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8
                public1.key checkpoint.key
            if b4
            then
              ok (core.result.Result.Err
                solana_program_error.ProgramError.InvalidArgument, sdk, guards)
            else
              if proof.is_signer
              then
                ok (core.result.Result.Err
                  solana_program_error.ProgramError.InvalidAccountData, sdk,
                  guards)
              else
                if proof.is_writable
                then
                  ok (core.result.Result.Err
                    solana_program_error.ProgramError.InvalidAccountData, sdk,
                    guards)
                else
                  if proof.executable
                  then
                    ok (core.result.Result.Err
                      solana_program_error.ProgramError.InvalidAccountData,
                      sdk, guards)
                  else
                    if public1.is_signer
                    then
                      ok (core.result.Result.Err
                        solana_program_error.ProgramError.InvalidAccountData,
                        sdk, guards)
                    else
                      if public1.is_writable
                      then
                        ok (core.result.Result.Err
                          solana_program_error.ProgramError.InvalidAccountData,
                          sdk, guards)
                      else
                        if public1.executable
                        then
                          ok (core.result.Result.Err
                            solana_program_error.ProgramError.InvalidAccountData,
                            sdk, guards)
                        else
                          let b5 ←
                            core.array.equality.PartialEqArray.ne
                              core.cmp.PartialEqU8 checkpoint.owner program_id
                          if b5
                          then
                            ok (core.result.Result.Err
                              solana_program_error.ProgramError.InvalidAccountData,
                              sdk, guards)
                          else
                            if checkpoint.is_signer
                            then
                              ok (core.result.Result.Err
                                solana_program_error.ProgramError.InvalidAccountData,
                                sdk, guards)
                            else
                              if checkpoint.executable
                              then
                                ok (core.result.Result.Err
                                  solana_program_error.ProgramError.InvalidAccountData,
                                  sdk, guards)
                              else
                                if checkpoint.is_writable
                                then
                                  let r ←
                                    owned_data_len sdk checkpoint.data_slot
                                  let cf ←
                                    core.result.Result.Insts.CoreOpsTry.branch
                                      r
                                  match cf with
                                  | core.ops.control_flow.ControlFlow.Continue
                                    val =>
                                    let i1 ←
                                      aspis_r1_cost_probe.verifier.checkpoint_size
                                        aspis_r1_cost_probe.transport.Variant.S2
                                    if val != i1
                                    then
                                      ok (core.result.Result.Err
                                        solana_program_error.ProgramError.InvalidAccountData,
                                        sdk, guards)
                                    else
                                      let (r1, sdk1, guards1) ←
                                        owned_acquire_checkpoint sdk guards
                                          checkpoint.data_slot
                                      let cf1 ←
                                        core.result.Result.Insts.CoreOpsTry.branch
                                          r1
                                      match cf1 with
                                      |
                                        core.ops.control_flow.ControlFlow.Continue
                                        _ =>
                                        let odc ←
                                          alloc.vec.Vec.index
                                            (core.slice.index.SliceIndexUsizeSlice
                                            OwnedDataCell) sdk1.data_cells
                                            checkpoint.data_slot
                                        let v ←
                                          alloc.vec.CloneVec.clone
                                            core.clone.CloneU8 odc.bytes
                                        let b6 ← owned_checkpoint_nonzero v
                                        if b6
                                        then
                                          ok (core.result.Result.Err
                                            solana_program_error.ProgramError.AccountAlreadyInitialized,
                                            sdk1, guards1)
                                        else
                                          let (r2, sdk2) ←
                                            owned_acquire_shared sdk1
                                              public1.data_slot
                                          let cf2 ←
                                            core.result.Result.Insts.CoreOpsTry.branch
                                              r2
                                          match cf2 with
                                          |
                                            core.ops.control_flow.ControlFlow.Continue
                                            _ =>
                                            let odc1 ←
                                              alloc.vec.Vec.index
                                                (core.slice.index.SliceIndexUsizeSlice
                                                OwnedDataCell) sdk2.data_cells
                                                public1.data_slot
                                            let public_data ←
                                              alloc.vec.CloneVec.clone
                                                core.clone.CloneU8 odc1.bytes
                                            let s :=
                                              alloc.vec.Vec.deref public_data
                                            let r3 ←
                                              (decode_public_statement_box ops) s
                                            let cf3 ←
                                              core.result.Result.Insts.CoreOpsTry.branch
                                                r3
                                            match cf3 with
                                            |
                                              core.ops.control_flow.ControlFlow.Continue
                                              val1 =>
                                              let r4 ←
                                                ops.op5
                                                  val1
                                              let r5 ←
                                                core.result.Result.map_err
                                                  owned_stage1_body.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError
                                                  r4 ()
                                              let cf4 ←
                                                core.result.Result.Insts.CoreOpsTry.branch
                                                  r5
                                              match cf4 with
                                              |
                                                core.ops.control_flow.ControlFlow.Continue
                                                _ =>
                                                let pvpftcv ←
                                                  aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.common
                                                    val1
                                                let r6 ←
                                                  ops.op8
                                                    pvpftcv.lane_transition.candidate_afterstate
                                                let r7 ←
                                                  core.result.Result.map_err
                                                    owned_stage1_body.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1ProgramError
                                                    r6 ()
                                                let cf5 ←
                                                  core.result.Result.Insts.CoreOpsTry.branch
                                                    r7
                                                match cf5 with
                                                |
                                                  core.ops.control_flow.ControlFlow.Continue
                                                  val2 =>
                                                  let (r8, sdk3) ←
                                                    owned_acquire_shared sdk2
                                                      proof.data_slot
                                                  let cf6 ←
                                                    core.result.Result.Insts.CoreOpsTry.branch
                                                      r8
                                                  match cf6 with
                                                  |
                                                    core.ops.control_flow.ControlFlow.Continue
                                                    _ =>
                                                    let odc2 ←
                                                      alloc.vec.Vec.index
                                                        (core.slice.index.SliceIndexUsizeSlice
                                                        OwnedDataCell)
                                                        sdk3.data_cells
                                                        proof.data_slot
                                                    let proof_data ←
                                                      alloc.vec.CloneVec.clone
                                                        core.clone.CloneU8
                                                        odc2.bytes
                                                    let proof_length ←
                                                      ops.op4
                                                    let proof_start ←
                                                      ops.op7
                                                    let o ←
                                                      lift (Usize.checked_add
                                                        proof_start
                                                        proof_length)
                                                    let r9 ←
                                                      ops.op2
                                                        o
                                                        solana_program_error.ProgramError.InvalidAccountData
                                                    let cf7 ←
                                                      core.result.Result.Insts.CoreOpsTry.branch
                                                        r9
                                                    match cf7 with
                                                    |
                                                      core.ops.control_flow.ControlFlow.Continue
                                                      val3 =>
                                                      let i2 :=
                                                        alloc.vec.Vec.len
                                                          proof_data
                                                      if i2 != val3
                                                      then
                                                        ok
                                                          (core.result.Result.Err
                                                          solana_program_error.ProgramError.InvalidAccountData,
                                                          sdk3,
                                                          {
                                                            guards1
                                                              with
                                                              «public» :=
                                                                (some
                                                                  public1.data_slot),
                                                              proof :=
                                                                (some
                                                                  proof.data_slot)
                                                          })
                                                      else
                                                        let s1 ←
                                                          alloc.vec.Vec.index
                                                            (core.slice.index.SliceIndexRangeToUsizeSlice
                                                            Std.U8) proof_data
                                                            {
                                                              «end» :=
                                                                proof_start
                                                            }
                                                        let b7 ←
                                                          prefixCmp s1 val2
                                                        if b7
                                                        then
                                                          ok
                                                            (core.result.Result.Err
                                                            solana_program_error.ProgramError.InvalidAccountData,
                                                            sdk3,
                                                            {
                                                              guards1
                                                                with
                                                                «public» :=
                                                                  (some
                                                                    public1.data_slot),
                                                                proof :=
                                                                  (some
                                                                    proof.data_slot)
                                                            })
                                                        else
                                                          let i3 ←
                                                            proof_start +
                                                              8#usize
                                                          let i4 ←
                                                            alloc.vec.Vec.index
                                                              (core.slice.index.SliceIndexUsizeSlice
                                                              Std.U8)
                                                              proof_data i3
                                                          let i5 ←
                                                            aspis_r1_cost_probe.transport.Variant.tag
                                                              aspis_r1_cost_probe.transport.Variant.S2
                                                          if i4 != i5
                                                          then
                                                            ok
                                                              (core.result.Result.Err
                                                              solana_program_error.ProgramError.InvalidAccountData,
                                                              sdk3,
                                                              {
                                                                guards1
                                                                  with
                                                                  «public» :=
                                                                    (some
                                                                    public1.data_slot),
                                                                  proof :=
                                                                    (some
                                                                    proof.data_slot)
                                                              })
                                                          else
                                                            let p ←
                                                              aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
                                                                val1
                                                            let s2 :=
                                                              alloc.vec.Vec.deref
                                                                public_data
                                                            let s3 ←
                                                              alloc.vec.Vec.index
                                                                (core.slice.index.SliceIndexRangeUsizeSlice
                                                                Std.U8)
                                                                proof_data
                                                                {
                                                                  start :=
                                                                    proof_start,
                                                                  «end» :=
                                                                    val3
                                                                }
                                                            let i6 ←
                                                              Slice.index_usize
                                                                data 1#usize
                                                            let i7 ←
                                                              lift
                                                                (UScalar.cast
                                                                .Usize i6)
                                                            let r10 ←
                                                              (first_decoded ops) p
                                                                s2 s3 i7
                                                            let cf8 ←
                                                              core.result.Result.Insts.CoreOpsTry.branch
                                                                r10
                                                            match cf8 with
                                                            |
                                                              core.ops.control_flow.ControlFlow.Continue
                                                              val4 =>
                                                              let i8 :=
                                                                alloc.vec.Vec.len
                                                                  val4
                                                              let odc3 ←
                                                                alloc.vec.Vec.index
                                                                  (core.slice.index.SliceIndexUsizeSlice
                                                                  OwnedDataCell)
                                                                  sdk3.data_cells
                                                                  checkpoint.data_slot
                                                              let i9 :=
                                                                alloc.vec.Vec.len
                                                                  odc3.bytes
                                                              if i8 != i9
                                                              then
                                                                ok
                                                                  (core.result.Result.Err
                                                                  solana_program_error.ProgramError.InvalidAccountData,
                                                                  sdk3,
                                                                  {
                                                                    guards1
                                                                    with
                                                                    «public» :=
                                                                    (some
                                                                    public1.data_slot),
                                                                    proof :=
                                                                    (some
                                                                    proof.data_slot)
                                                                  })
                                                              else
                                                                let (odc4,
                                                                  index_mut_back)
                                                                  ←
                                                                  alloc.vec.Vec.index_mut
                                                                    (core.slice.index.SliceIndexUsizeSlice
                                                                    OwnedDataCell)
                                                                    sdk3.data_cells
                                                                    checkpoint.data_slot
                                                                let v1 :=
                                                                  index_mut_back
                                                                    {
                                                                    odc4
                                                                    with
                                                                    bytes :=
                                                                    val4
                                                                    }
                                                                ok
                                                                  (core.result.Result.Ok
                                                                  (),
                                                                  {
                                                                    sdk3
                                                                    with
                                                                    data_cells :=
                                                                    v1
                                                                  },
                                                                  {
                                                                    guards1
                                                                    with
                                                                    «public» :=
                                                                    (some
                                                                    public1.data_slot),
                                                                    proof :=
                                                                    (some
                                                                    proof.data_slot)
                                                                  })
                                                            |
                                                              core.ops.control_flow.ControlFlow.Break
                                                              residual =>
                                                              let r11 ←
                                                                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                                  Unit
                                                                  (core.convert.FromSame
                                                                  solana_program_error.ProgramError)
                                                                  residual
                                                              ok (r11, sdk3,
                                                                {
                                                                  guards1
                                                                    with
                                                                    «public» :=
                                                                    (some
                                                                    public1.data_slot),
                                                                    proof :=
                                                                    (some
                                                                    proof.data_slot)
                                                                })
                                                    |
                                                      core.ops.control_flow.ControlFlow.Break
                                                      residual =>
                                                      let r10 ←
                                                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                          Unit
                                                          (core.convert.FromSame
                                                          solana_program_error.ProgramError)
                                                          residual
                                                      ok (r10, sdk3,
                                                        {
                                                          guards1
                                                            with
                                                            «public» :=
                                                              (some
                                                                public1.data_slot),
                                                            proof :=
                                                              (some
                                                                proof.data_slot)
                                                        })
                                                  |
                                                    core.ops.control_flow.ControlFlow.Break
                                                    residual =>
                                                    let r9 ←
                                                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                        Unit
                                                        (core.convert.FromSame
                                                        solana_program_error.ProgramError)
                                                        residual
                                                    ok (r9, sdk3,
                                                      {
                                                        guards1
                                                          with
                                                          «public» :=
                                                            (some
                                                              public1.data_slot)
                                                      })
                                                |
                                                  core.ops.control_flow.ControlFlow.Break
                                                  residual =>
                                                  let r8 ←
                                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                      Unit
                                                      (core.convert.FromSame
                                                      solana_program_error.ProgramError)
                                                      residual
                                                  ok (r8, sdk2,
                                                    {
                                                      guards1
                                                        with
                                                        «public» :=
                                                          (some
                                                            public1.data_slot)
                                                    })
                                              |
                                                core.ops.control_flow.ControlFlow.Break
                                                residual =>
                                                let r6 ←
                                                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                    Unit (core.convert.FromSame
                                                    solana_program_error.ProgramError)
                                                    residual
                                                ok (r6, sdk2,
                                                  {
                                                    guards1
                                                      with
                                                      «public» :=
                                                        (some
                                                          public1.data_slot)
                                                  })
                                            |
                                              core.ops.control_flow.ControlFlow.Break
                                              residual =>
                                              let r4 ←
                                                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                  Unit (core.convert.FromSame
                                                  solana_program_error.ProgramError)
                                                  residual
                                              ok (r4, sdk2,
                                                {
                                                  guards1
                                                    with
                                                    «public» :=
                                                      (some public1.data_slot)
                                                })
                                          |
                                            core.ops.control_flow.ControlFlow.Break
                                            residual =>
                                            let r3 ←
                                              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                Unit (core.convert.FromSame
                                                solana_program_error.ProgramError)
                                                residual
                                            ok (r3, sdk2, guards1)
                                      | core.ops.control_flow.ControlFlow.Break
                                        residual =>
                                        let r2 ←
                                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                            Unit (core.convert.FromSame
                                            solana_program_error.ProgramError)
                                            residual
                                        ok (r2, sdk1, guards1)
                                  | core.ops.control_flow.ControlFlow.Break
                                    residual =>
                                    let r1 ←
                                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                        Unit (core.convert.FromSame
                                        solana_program_error.ProgramError)
                                        residual
                                    ok (r1, sdk, guards)
                                else
                                  ok (core.result.Result.Err
                                    solana_program_error.ProgramError.InvalidAccountData,
                                    sdk, guards)
    else
      ok (core.result.Result.Err
        solana_program_error.ProgramError.InvalidInstructionData, sdk, guards)


/-- Both original comparison sites, including every error continuation, are
retained. No accepted-run or size premise is required for this exact fission. -/
theorem body_factor (ops : Ops) (program : Array U8 32#usize) (sdk : OwnedSdk)
    (data : Slice U8) (guards : LiveGuards) :
    owned_stage1_body ops program sdk data guards=
      bodyWithPrefixCmp (fun bytes candidate => ops.op0 core.cmp.PartialEqU8 bytes candidate)
        ops program sdk data guards := by
  snapshot_defeq

/-- The complete installed reference consumes the scalar-loop correspondence.
No prefix/tag pass, comparator success or length premise is supplied. -/
theorem body_eq_loop (ops : Ops) (verifierOps : AspisR1CurrentCaller.Ops)
    (program : Array U8 32#usize) (sdk : OwnedSdk) (data : Slice U8) (guards : LiveGuards) :
    owned_stage1_body (Installation.install ops verifierOps) program sdk data guards=
      bodyWithPrefixCmp loopCmp (Installation.install ops verifierOps) program sdk data guards := by
  rw [body_factor]
  change bodyWithPrefixCmp stdCmp _ _ _ _ _=bodyWithPrefixCmp loopCmp _ _ _ _ _
  rw [cmp_eq]

def stage1 (ops : Ops) (verifierOps : AspisR1CurrentCaller.Ops)
    (program : Array U8 32#usize) (sdk : OwnedSdk) (data : alloc.vec.Vec U8) := do
  let (status,heap,guards) ← bodyWithPrefixCmp loopCmp (Installation.install ops verifierOps)
    program sdk (alloc.vec.Vec.deref data) {checkpoint:=none,«public»:=none,proof:=none}
  let out ← owned_release_guards heap guards
  ok (status,out)

/-- Complete installed stage1 equality includes every status and final cleanup. -/
theorem stage1_eq (ops : Ops) (verifierOps : AspisR1CurrentCaller.Ops)
    (program : Array U8 32#usize) (sdk : OwnedSdk) (data : alloc.vec.Vec U8) :
    stage1 ops verifierOps program sdk data=
      owned_stage1 (Installation.install ops verifierOps) program sdk data := by
  unfold stage1 owned_stage1
  dsimp only
  rw [←body_eq_loop]
  congr 1
  funext state
  rcases state with ⟨status,heap,guards⟩
  rfl

#print axioms cmp_eq
#print axioms body_factor
#print axioms body_eq_loop
#print axioms stage1_eq
end AspisS2OwnedStage1.SdkReference.ProofPrefixParent
