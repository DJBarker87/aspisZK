import Hiq_PoolSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.PoolM_NativeCancelSource
open Aeneas Aeneas.Std Result ControlFlow Error
abbrev solana_pubkey.Pubkey := AdapterRw.solana_pubkey.Pubkey
abbrev solana_account_info.AccountInfo := AdapterRw.Cuts.Account
abbrev solana_program_error.ProgramError := AdapterRw.solana_program_error.ProgramError
inductive error.PoolV1ProgramError where
| InvalidAccountType : error.PoolV1ProgramError
| InvalidRootPageAddress : error.PoolV1ProgramError
| StateHistoryMismatch : error.PoolV1ProgramError
| TreeFull : error.PoolV1ProgramError
| InsufficientTreeCapacity : error.PoolV1ProgramError
| UnexpectedRootPage : error.PoolV1ProgramError
| NonCanonicalLeaf : error.PoolV1ProgramError
| ArithmeticOverflow : error.PoolV1ProgramError
| InvalidPoolStateAddress : error.PoolV1ProgramError
| InvalidVerifierRegistryAddress : error.PoolV1ProgramError
| InvalidVerifierEntryAddress : error.PoolV1ProgramError
| InvalidVerifierRegistry : error.PoolV1ProgramError
| InvalidVerifierEntry : error.PoolV1ProgramError
| VerifierRegistryPaused : error.PoolV1ProgramError
| VerifierEntryInactive : error.PoolV1ProgramError
| VerifierEntryNotActiveYet : error.PoolV1ProgramError
| VerifierEntryRetired : error.PoolV1ProgramError
| VerifierSelectionMismatch : error.PoolV1ProgramError
| InvalidTokenProgram : error.PoolV1ProgramError
| InvalidMint : error.PoolV1ProgramError
| InvalidTokenAccount : error.PoolV1ProgramError
| InvalidVaultAuthority : error.PoolV1ProgramError
| InvalidVaultTokenAddress : error.PoolV1ProgramError
| InvalidDepositAmount : error.PoolV1ProgramError
| InsufficientDepositFunds : error.PoolV1ProgramError
| UnsupportedTokenConfiguration : error.PoolV1ProgramError
| InvalidEncryptedNotePayload : error.PoolV1ProgramError
| TokenBalanceDeltaMismatch : error.PoolV1ProgramError
| InvalidSourceAuthority : error.PoolV1ProgramError
| InvalidHistoricalAnchorEnvelope : error.PoolV1ProgramError
| HistoricalAnchorIdentityMismatch : error.PoolV1ProgramError
| HistoricalAnchorSelectionMismatch : error.PoolV1ProgramError
| HistoricalAnchorInFuture : error.PoolV1ProgramError
| InvalidHistoricalAnchorPage : error.PoolV1ProgramError
| HistoricalAnchorRootMismatch : error.PoolV1ProgramError
| InvalidNullifierMarkerAddress : error.PoolV1ProgramError
| InvalidNullifierMarkerAccount : error.PoolV1ProgramError
| NullifierAlreadyConsumed : error.PoolV1ProgramError
| InvalidVerifierProgramAccount : error.PoolV1ProgramError
| InvalidVerifierProofAccount : error.PoolV1ProgramError
| VerifierProofBindingMismatch : error.PoolV1ProgramError
| InvalidVerifierDispatchEnvelope : error.PoolV1ProgramError
| VerifierDispatchIdentityMismatch : error.PoolV1ProgramError
| InvalidVerifierReturnProgram : error.PoolV1ProgramError
| InvalidVerifierReturnData : error.PoolV1ProgramError
| VerifierResultBindingMismatch : error.PoolV1ProgramError
| MissingVerifierReturnData : error.PoolV1ProgramError
| InvalidWithdrawalAmount : error.PoolV1ProgramError
| InsufficientVaultFunds : error.PoolV1ProgramError
| InvalidDestinationTokenAccount : error.PoolV1ProgramError
| InvalidSystemProgram : error.PoolV1ProgramError
| InvalidPayer : error.PoolV1ProgramError
| InvalidFreshAccount : error.PoolV1ProgramError
| CpiInvocationForbidden : error.PoolV1ProgramError

def solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey.eq := Hist_Authority.keyEq

def solana_program_error.ProgramError.Insts.CoreConvertFromPoolV1ProgramError.from
    (e : error.PoolV1ProgramError) : Result solana_program_error.ProgramError :=
  ok (.Custom (match e with
    | .InvalidAccountType => 1095966721#u32
    | .InvalidRootPageAddress => 1095966722#u32
    | .StateHistoryMismatch => 1095966723#u32
    | .TreeFull => 1095966724#u32
    | .InsufficientTreeCapacity => 1095966725#u32
    | .UnexpectedRootPage => 1095966726#u32
    | .NonCanonicalLeaf => 1095966727#u32
    | .ArithmeticOverflow => 1095966728#u32
    | .InvalidPoolStateAddress => 1095966729#u32
    | .InvalidVerifierRegistryAddress => 1095966730#u32
    | .InvalidVerifierEntryAddress => 1095966731#u32
    | .InvalidVerifierRegistry => 1095966732#u32
    | .InvalidVerifierEntry => 1095966733#u32
    | .VerifierRegistryPaused => 1095966734#u32
    | .VerifierEntryInactive => 1095966735#u32
    | .VerifierEntryNotActiveYet => 1095966736#u32
    | .VerifierEntryRetired => 1095966737#u32
    | .VerifierSelectionMismatch => 1095966738#u32
    | .InvalidTokenProgram => 1095966739#u32
    | .InvalidMint => 1095966740#u32
    | .InvalidTokenAccount => 1095966741#u32
    | .InvalidVaultAuthority => 1095966742#u32
    | .InvalidVaultTokenAddress => 1095966743#u32
    | .InvalidDepositAmount => 1095966744#u32
    | .InsufficientDepositFunds => 1095966745#u32
    | .UnsupportedTokenConfiguration => 1095966746#u32
    | .InvalidEncryptedNotePayload => 1095966747#u32
    | .TokenBalanceDeltaMismatch => 1095966748#u32
    | .InvalidSourceAuthority => 1095966749#u32
    | .InvalidHistoricalAnchorEnvelope => 1095966750#u32
    | .HistoricalAnchorIdentityMismatch => 1095966751#u32
    | .HistoricalAnchorSelectionMismatch => 1095966752#u32
    | .HistoricalAnchorInFuture => 1095966753#u32
    | .InvalidHistoricalAnchorPage => 1095966754#u32
    | .HistoricalAnchorRootMismatch => 1095966755#u32
    | .InvalidNullifierMarkerAddress => 1095966756#u32
    | .InvalidNullifierMarkerAccount => 1095966757#u32
    | .NullifierAlreadyConsumed => 1095966758#u32
    | .InvalidVerifierProgramAccount => 1095966759#u32
    | .InvalidVerifierProofAccount => 1095966760#u32
    | .VerifierProofBindingMismatch => 1095966761#u32
    | .InvalidVerifierDispatchEnvelope => 1095966762#u32
    | .VerifierDispatchIdentityMismatch => 1095966763#u32
    | .InvalidVerifierReturnProgram => 1095966764#u32
    | .InvalidVerifierReturnData => 1095966765#u32
    | .VerifierResultBindingMismatch => 1095966766#u32
    | .MissingVerifierReturnData => 1095966767#u32
    | .InvalidWithdrawalAmount => 1095966768#u32
    | .InsufficientVaultFunds => 1095966769#u32
    | .InvalidDestinationTokenAccount => 1095966770#u32
    | .InvalidSystemProgram => 1095966771#u32
    | .InvalidPayer => 1095966772#u32
    | .InvalidFreshAccount => 1095966773#u32
    | .CpiInvocationForbidden => 1095966774#u32
))
def POOL_V1_PREPARED_SETTLEMENT_CORE_ACCOUNT_BYTES : Result Usize := ok 10000#usize
def POOL_V1_PREPARED_SETTLEMENT_ROLLOVER_ACCOUNT_BYTES : Result Usize := ok 8504#usize
/-- Trait implementation: [solana_pubkey::{impl core::cmp::PartialEq<solana_pubkey::Pubkey> for solana_pubkey::Pubkey}]
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/solana-pubkey-2.4.0/src/lib.rs', lines 164:40-164:49
    Name pattern: [core::cmp::PartialEq<solana_pubkey::Pubkey, solana_pubkey::Pubkey>] -/
@[reducible, rust_trait_impl
  "core::cmp::PartialEq<solana_pubkey::Pubkey, solana_pubkey::Pubkey>"]
impl_def solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey : core.cmp.PartialEq
  solana_pubkey.Pubkey solana_pubkey.Pubkey := {
  eq := solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey.eq
  ne := core.cmp.PartialEq.ne.trait_default
    solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey
}

/-- [poolm_slice::require_prepared_plan_account_v1]:
    Source: 'PoolM_lib.rs', lines 19:0-33:1 -/
def require_prepared_plan_account_v1
  (readLength : solana_account_info.AccountInfo → Result Usize)
  (account : solana_account_info.AccountInfo)
  (program_id : solana_pubkey.Pubkey) (exact_data_len : Std.Usize) :
  Result (core.result.Result Unit solana_program_error.ProgramError)
  := do
  let b ←
    core.cmp.impls.PartialEqShared.ne
      solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey account.owner
      program_id
  if b
  then
    ok (core.result.Result.Err
      solana_program_error.ProgramError.InvalidAccountData)
  else
    if account.executable
    then
      ok (core.result.Result.Err
        solana_program_error.ProgramError.InvalidAccountData)
    else
      if account.is_signer
      then
        ok (core.result.Result.Err
          solana_program_error.ProgramError.InvalidAccountData)
      else
        if account.is_writable
        then
          let i ← readLength account
          if i != exact_data_len
          then
            ok (core.result.Result.Err
              solana_program_error.ProgramError.InvalidAccountData)
          else ok (core.result.Result.Ok ())
        else
          ok (core.result.Result.Err
            solana_program_error.ProgramError.InvalidAccountData)

/-- Trait implementation: [poolm_slice::error::{impl core::convert::From<poolm_slice::error::PoolV1ProgramError> for solana_program_error::ProgramError}]
    Source: 'error.rs', lines 62:0-66:1 -/
@[reducible]
def solana_program_error.ProgramError.Insts.CoreConvertFromPoolV1ProgramError :
  core.convert.From solana_program_error.ProgramError error.PoolV1ProgramError
  := {
  «from» :=
    solana_program_error.ProgramError.Insts.CoreConvertFromPoolV1ProgramError.from
}

/-- [poolm_slice::PoolM_cancel_roles_native]:
    Source: 'PoolM_lib.rs', lines 76:0-89:1
    Visibility: public -/
def PoolM_cancel_roles_native
  (readLength : solana_account_info.AccountInfo → Result Usize) (system : solana_pubkey.Pubkey)
  (program_id : solana_pubkey.Pubkey)
  (plan_authority : solana_account_info.AccountInfo)
  (core_plan : solana_account_info.AccountInfo)
  (shard : solana_account_info.AccountInfo) (has_shard : Bool) :
  Result (core.result.Result Unit solana_program_error.ProgramError)
  := do
  if plan_authority.is_signer
  then
    if plan_authority.is_writable
    then
      if plan_authority.executable
      then
        let pe ←
          core.convert.IntoFrom.into
            solana_program_error.ProgramError.Insts.CoreConvertFromPoolV1ProgramError
            error.PoolV1ProgramError.InvalidPayer
        ok (core.result.Result.Err pe)
      else
        let p ← ok system
        let b ←
          core.cmp.impls.PartialEqShared.ne
            solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey
            plan_authority.owner p
        if b
        then
          let pe ←
            core.convert.IntoFrom.into
              solana_program_error.ProgramError.Insts.CoreConvertFromPoolV1ProgramError
              error.PoolV1ProgramError.InvalidPayer
          ok (core.result.Result.Err pe)
        else
          let i ← POOL_V1_PREPARED_SETTLEMENT_CORE_ACCOUNT_BYTES
          let r ← require_prepared_plan_account_v1 readLength core_plan program_id i
          let cf ← core.result.Result.Insts.CoreOpsTry.branch r
          match cf with
          | core.ops.control_flow.ControlFlow.Continue _ =>
            if has_shard
            then
              let i1 ← POOL_V1_PREPARED_SETTLEMENT_ROLLOVER_ACCOUNT_BYTES
              let r1 ← require_prepared_plan_account_v1 readLength shard program_id i1
              let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
              match cf1 with
              | core.ops.control_flow.ControlFlow.Continue _ =>
                ok (core.result.Result.Ok ())
              | core.ops.control_flow.ControlFlow.Break residual =>
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                  Unit (core.convert.FromSame
                  solana_program_error.ProgramError) residual
            else ok (core.result.Result.Ok ())
          | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              Unit (core.convert.FromSame solana_program_error.ProgramError)
              residual
    else
      let pe ←
        core.convert.IntoFrom.into
          solana_program_error.ProgramError.Insts.CoreConvertFromPoolV1ProgramError
          error.PoolV1ProgramError.InvalidPayer
      ok (core.result.Result.Err pe)
  else
    let pe ←
      core.convert.IntoFrom.into
        solana_program_error.ProgramError.Insts.CoreConvertFromPoolV1ProgramError
        error.PoolV1ProgramError.InvalidPayer
    ok (core.result.Result.Err pe)

end AspisR1.PoolM_NativeCancelSource
end
