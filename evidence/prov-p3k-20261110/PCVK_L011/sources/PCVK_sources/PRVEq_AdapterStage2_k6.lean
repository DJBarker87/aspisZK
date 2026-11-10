-- PCVK_ AdapterRw stage2: fresh = gate. Fresh text: PCVJ emission (Aeneas b59d5188-extended, overflow ON, frozen 4bb3b3f), externals as fields of Ext.
-- RESULT CLASS: CONDITIONAL_ON_BINDING (see Bound). Statement: for every ops and x with Bound ops x, fresh x = gate ops.
import Aeneas
import AdapterRwModel
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace AdapterRw
namespace PCVK_S2

structure Ext where
  Hash : Type
  aspis_statement_pool_v1_pair_forest_terminal_encode_pool_v1_pair_forest_terminal_statement_v1 : aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1 → Result (core.result.Result (Array Std.U8 1880#usize) aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
  aspis_statement_pool_v1_pair_forest_terminal_decode_pool_v1_pair_forest_terminal_request_v1 : (Slice Std.U8) → Result (core.result.Result aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalRequestV1 aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
  aspis_statement_pool_v1_pair_forest_terminal_POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES : Result Std.Usize
  aspis_statement_pool_v1_pair_forest_terminal_PoolV1PairForestTerminalPaymentV1_nullifier : aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalPaymentV1 → Result (Array aspis_core.field.M31 8#usize)
  aspis_statement_pool_v1_pair_forest_terminal_POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_MAGIC : Result (Array Std.U8 4#usize)
  aspis_statement_pool_v1_pair_forest_terminal_POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES : Result Std.Usize
  core_ops_range_RangeFull_Insts_CoreSliceIndexSliceIndexSliceSlice_get_unchecked_mut : ∀ {T : Type}, core.ops.range.RangeFull → (MutRawPtr (Slice T)) → Result (MutRawPtr (Slice T))
  core_ops_range_RangeFull_Insts_CoreSliceIndexSliceIndexSliceSlice_get_unchecked : ∀ {T : Type}, core.ops.range.RangeFull → (ConstRawPtr (Slice T)) → Result (ConstRawPtr (Slice T))
  aspis_statement_pool_v1_pair_forest_accounts_POOL_V1_PAIR_FOREST_ALL_LANES_MASK : Result Std.U8
  aspis_statement_pool_v1_pair_forest_accounts_pool_v1_pair_forest_output_lane_v1 : (Array aspis_core.field.M31 8#usize) → Result (core.result.Result Std.U8 aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1)
  aspis_statement_pool_v1_pair_terminal_POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES : Result Std.Usize
  core_ops_range_RangeFull_Insts_CoreSliceIndexSliceIndexSliceSlice_index_mut : ∀ {T : Type}, core.ops.range.RangeFull → (Slice T) → Result ((Slice T) × (Slice T → Slice T))
  core_ops_range_RangeFull_Insts_CoreSliceIndexSliceIndexSliceSlice_get_mut : ∀ {T : Type}, core.ops.range.RangeFull → (Slice T) → Result ((Option (Slice T)) × (Option (Slice T) → Slice T))
  core_ops_range_RangeFull_Insts_CoreSliceIndexSliceIndexSliceSlice_index : ∀ {T : Type}, core.ops.range.RangeFull → (Slice T) → Result (Slice T)
  core_ops_range_RangeFull_Insts_CoreSliceIndexSliceIndexSliceSlice_get : ∀ {T : Type}, core.ops.range.RangeFull → (Slice T) → Result (Option (Slice T))
  r1_pool_adapter_owned_authenticate_invariant_release_registry : solana_pubkey.Pubkey → solana_pubkey.Pubkey → r1_pool_adapter.owned.OwnedAccount → aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1 → r1_pool_adapter.owned.OwnedAccount → r1_pool_adapter.owned.OwnedAccount → Std.U64 → Result (core.result.Result Unit solana_program_error.ProgramError)
  solana_program_error_ProgramError_Insts_CoreCloneClone_clone : solana_program_error.ProgramError → Result solana_program_error.ProgramError
  solana_pubkey_Pubkey_Insts_CoreConvertAsRefSliceU8_as_ref : solana_pubkey.Pubkey → Result (Slice Std.U8)
  aspis_r1_cost_probe_verifier_candidate_tx2_authenticated : ∀ {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H), (Slice Std.U8) → (Slice Std.U8) → (Slice Std.U8) → H → (Option (aspis_r1_cost_probe.verifier.Phase → Result Unit)) → Result (core.result.Result Unit aspis_r1_cost_probe.verifier.Error)
  solana_pubkey_Pubkey_Insts_CoreCmpPartialEqPubkey_eq : solana_pubkey.Pubkey → solana_pubkey.Pubkey → Result Bool
  core_option_Option_Insts_CoreCmpPartialEqOption_eq : ∀ {T : Type} (cmpPartialEqInst : core.cmp.PartialEq T T), (Option T) → (Option T) → Result Bool
  r1_pool_adapter_owned_require_verifier_checkpoint : r1_pool_adapter.owned.OwnedAccount → solana_pubkey.Pubkey → Bool → Result (core.result.Result Unit solana_program_error.ProgramError)
  r1_pool_adapter_owned_require_distinct_accounts : ∀ {N : Std.Usize}, (Array r1_pool_adapter.owned.OwnedAccount N) → Result (core.result.Result Unit solana_program_error.ProgramError)
  r1_pool_adapter_owned_require_readonly_account : r1_pool_adapter.owned.OwnedAccount → solana_pubkey.Pubkey → Result (core.result.Result Unit solana_program_error.ProgramError)
  r1_pool_adapter_decode_lane_from_pool_release : (Slice Std.U8) → Result (core.result.Result aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestLaneStateV1 solana_program_error.ProgramError)
  r1_pool_adapter_owned_require_readonly_buffer : r1_pool_adapter.owned.OwnedAccount → Result (core.result.Result Unit solana_program_error.ProgramError)
  solana_pubkey_Pubkey_create_program_address : (Slice (Slice Std.U8)) → solana_pubkey.Pubkey → Result (core.result.Result solana_pubkey.Pubkey solana_pubkey.PubkeyError)
  r1_pool_adapter_reconstruct_asq8_statement : aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalRequestV1 → r1_pool_adapter.AuthenticatedAsq8Accounts → aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 → Result (core.result.Result aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1 solana_program_error.ProgramError)
  r1_pool_adapter_decode_checkpoint_box : (Slice Std.U8) → Result (core.result.Result aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestCheckpointV1 solana_program_error.ProgramError)
  solana_pubkey_Pubkey_new_from_array : (Array Std.U8 32#usize) → Result solana_pubkey.Pubkey
  r1_pool_adapter_decode_master_box : (Slice Std.U8) → Result (core.result.Result aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1 solana_program_error.ProgramError)
  r1_pool_adapter_scan_proof_buffer : (Slice Std.U8) → Result (core.result.Result r1_pool_adapter.ScannedAsqaProof solana_program_error.ProgramError)
  r1_pool_adapter_pool_program_id : Result (Array Std.U8 32#usize)
  solana_pubkey_Pubkey_to_bytes : solana_pubkey.Pubkey → Result (Array Std.U8 32#usize)
  r1_pool_adapter_emit_result : aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1 → Result (core.result.Result Unit solana_program_error.ProgramError)
  solana_sha256_hasher_hashv : (Slice (Slice Std.U8)) → Result Hash
  solana_hash_Hash_to_bytes : Hash → Result (Array Std.U8 32#usize)
  core_slice_Slice_first : ∀ {T : Type}, (Slice T) → Result (Option T)
  observer : Result (Option (aspis_r1_cost_probe.verifier.Phase → Result Unit))
  error : aspis_r1_cost_probe.verifier.Error → Result solana_program_error.ProgramError

@[rust_fun "core::option::{core::option::Option<@T>}::ok_or"]
def core.option.Option.ok_or
  {T : Type} {E : Type} (self : Option T) (err : E) :
  Result (core.result.Result T E)
  := do
  match self with
  | none => ok (core.result.Result.Err err)
  | some v => ok (core.result.Result.Ok v)

@[reducible, rust_trait_impl
  "core::cmp::PartialEq<core::option::Option<@T>, core::option::Option<@T>>"]
impl_def core.option.Option.Insts.CoreCmpPartialEqOption (x : Ext) {T : Type}
  (cmpPartialEqInst : core.cmp.PartialEq T T) : core.cmp.PartialEq (Option T)
  (Option T) := {
  eq := x.core_option_Option_Insts_CoreCmpPartialEqOption_eq cmpPartialEqInst
  ne := core.cmp.PartialEq.ne.trait_default
    (core.option.Option.Insts.CoreCmpPartialEqOption x cmpPartialEqInst)
}

@[reducible, rust_trait_impl "core::cmp::PartialEq<[@T], [@U]>"]
impl_def Slice.Insts.CoreCmpPartialEqSlice {T : Type} {U : Type}
  (cmpPartialEqInst : core.cmp.PartialEq T U) : core.cmp.PartialEq (Slice T)
  (Slice U) := {
  eq := core.slice.cmp.PartialEqSlice.eq cmpPartialEqInst
  ne := core.cmp.PartialEq.ne.trait_default (Slice.Insts.CoreCmpPartialEqSlice
    cmpPartialEqInst)
}

@[reducible, rust_trait_impl
  "core::slice::index::private_slice_index::Sealed<core::ops::range::RangeFull>"]
def core.ops.range.RangeFull.Insts.CoreSliceIndexPrivate_slice_indexSealed :
  core.slice.index.private_slice_index.Sealed core.ops.range.RangeFull := {
}

@[reducible, rust_trait_impl
  "core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>"]
def core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice (x : Ext) (T :
  Type) : core.slice.index.SliceIndex core.ops.range.RangeFull (Slice T) (Slice
  T) := {
  sealedInst :=
    core.ops.range.RangeFull.Insts.CoreSliceIndexPrivate_slice_indexSealed
  get := x.core_ops_range_RangeFull_Insts_CoreSliceIndexSliceIndexSliceSlice_get
  get_mut :=
    x.core_ops_range_RangeFull_Insts_CoreSliceIndexSliceIndexSliceSlice_get_mut
  get_unchecked :=
    x.core_ops_range_RangeFull_Insts_CoreSliceIndexSliceIndexSliceSlice_get_unchecked
  get_unchecked_mut :=
    x.core_ops_range_RangeFull_Insts_CoreSliceIndexSliceIndexSliceSlice_get_unchecked_mut
  index :=
    x.core_ops_range_RangeFull_Insts_CoreSliceIndexSliceIndexSliceSlice_index
  index_mut :=
    x.core_ops_range_RangeFull_Insts_CoreSliceIndexSliceIndexSliceSlice_index_mut
}

@[reducible, rust_trait_impl
  "core::cmp::PartialEq<solana_pubkey::Pubkey, solana_pubkey::Pubkey>"]
impl_def solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey (x : Ext) : core.cmp.PartialEq
  solana_pubkey.Pubkey solana_pubkey.Pubkey := {
  eq := x.solana_pubkey_Pubkey_Insts_CoreCmpPartialEqPubkey_eq
  ne := core.cmp.PartialEq.ne.trait_default
    (solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey x)
}

def SolanaDigest.Insts.CoreCloneClone.clone
  (self : SolanaDigest) : Result SolanaDigest := do
  ok self

@[reducible]
def SolanaDigest.Insts.CoreCloneClone : core.clone.Clone SolanaDigest := {
  clone := SolanaDigest.Insts.CoreCloneClone.clone
}

@[reducible]
def SolanaDigest.Insts.CoreMarkerCopy : core.marker.Copy SolanaDigest := {
  cloneInst := SolanaDigest.Insts.CoreCloneClone
}

def SolanaDigest.Insts.Aspis_coreDigestDigest32.digest (x : Ext)
  (self : SolanaDigest) (parts : Slice (Slice Std.U8)) :
  Result (Array Std.U8 32#usize)
  := do
  let h ← x.solana_sha256_hasher_hashv parts
  x.solana_hash_Hash_to_bytes h

@[reducible]
def SolanaDigest.Insts.Aspis_coreDigestDigest32 (x : Ext) : aspis_core.digest.Digest32
  SolanaDigest := {
  coremarkerCopyInst := SolanaDigest.Insts.CoreMarkerCopy
  digest := (SolanaDigest.Insts.Aspis_coreDigestDigest32.digest x)
}

@[global_simps, irreducible]
def r1_pool_adapter.PROFILE_BINDING : Array Std.U8 32#usize :=
  Array.make 32#usize [
    87#u8, 148#u8, 115#u8, 19#u8, 210#u8, 50#u8, 100#u8, 26#u8, 216#u8, 21#u8,
    125#u8, 102#u8, 191#u8, 175#u8, 250#u8, 177#u8, 30#u8, 76#u8, 58#u8,
    153#u8, 51#u8, 29#u8, 24#u8, 244#u8, 75#u8, 250#u8, 202#u8, 182#u8, 137#u8,
    151#u8, 55#u8, 211#u8
    ]

@[global_simps, irreducible]
def r1_pool_adapter.RELEASE_BINDING : Array Std.U8 32#usize :=
  Array.make 32#usize [
    226#u8, 148#u8, 175#u8, 188#u8, 20#u8, 239#u8, 106#u8, 254#u8, 118#u8,
    184#u8, 71#u8, 222#u8, 244#u8, 68#u8, 82#u8, 248#u8, 76#u8, 195#u8, 114#u8,
    128#u8, 100#u8, 101#u8, 118#u8, 7#u8, 181#u8, 68#u8, 165#u8, 57#u8, 202#u8,
    155#u8, 50#u8, 58#u8
    ]

@[global_simps, irreducible]
def r1_pool_adapter.PAIR_FOREST_MASTER_SEED : Slice Std.U8 :=
  Array.to_slice
    (Array.make 27#usize [
      97#u8, 115#u8, 112#u8, 105#u8, 115#u8, 45#u8, 112#u8, 97#u8, 105#u8,
      114#u8, 45#u8, 102#u8, 111#u8, 114#u8, 101#u8, 115#u8, 116#u8, 45#u8,
      109#u8, 97#u8, 115#u8, 116#u8, 101#u8, 114#u8, 45#u8, 118#u8, 49#u8
      ])

@[global_simps, irreducible]
def r1_pool_adapter.PAIR_FOREST_LANE_SEED : Slice Std.U8 :=
  Array.to_slice
    (Array.make 25#usize [
      97#u8, 115#u8, 112#u8, 105#u8, 115#u8, 45#u8, 112#u8, 97#u8, 105#u8,
      114#u8, 45#u8, 102#u8, 111#u8, 114#u8, 101#u8, 115#u8, 116#u8, 45#u8,
      108#u8, 97#u8, 110#u8, 101#u8, 45#u8, 118#u8, 49#u8
      ])

@[global_simps, irreducible]
def r1_pool_adapter.PAIR_FOREST_CHECKPOINT_SEED : Slice Std.U8 :=
  Array.to_slice
    (Array.make 31#usize [
      97#u8, 115#u8, 112#u8, 105#u8, 115#u8, 45#u8, 112#u8, 97#u8, 105#u8,
      114#u8, 45#u8, 102#u8, 111#u8, 114#u8, 101#u8, 115#u8, 116#u8, 45#u8,
      99#u8, 104#u8, 101#u8, 99#u8, 107#u8, 112#u8, 111#u8, 105#u8, 110#u8,
      116#u8, 45#u8, 118#u8, 49#u8
      ])

def r1_pool_adapter.owned.OwnedAccount.impl.key
  (self : r1_pool_adapter.owned.OwnedAccount) :
  Result solana_pubkey.Pubkey
  := do
  ok self.key

def r1_pool_adapter.owned.OwnedAccount.data (x : Ext)
  (self : r1_pool_adapter.owned.OwnedAccount) :
  Result (core.result.Result (Slice Std.U8) solana_program_error.ProgramError)
  := do
  match self.bytes with
  | core.result.Result.Ok bytes =>
    let s := alloc.vec.Vec.deref bytes
    ok (core.result.Result.Ok s)
  | core.result.Result.Err error1 =>
    let pe ←
      x.solana_program_error_ProgramError_Insts_CoreCloneClone_clone error1
    ok (core.result.Result.Err pe)

def
  r1_pool_adapter.owned.authenticate_asq8_accounts.closure_2.Insts.CoreOpsFunctionFnOnceTuplePubkeyErrorProgramError.call_once
  (c : r1_pool_adapter.owned.authenticate_asq8_accounts.closure_2)
  (tupled_args : solana_pubkey.PubkeyError) :
  Result solana_program_error.ProgramError
  := do
  ok solana_program_error.ProgramError.InvalidAccountData

@[reducible]
def
  r1_pool_adapter.owned.authenticate_asq8_accounts.closure_2.Insts.CoreOpsFunctionFnOnceTuplePubkeyErrorProgramError
  : core.ops.function.FnOnce
  r1_pool_adapter.owned.authenticate_asq8_accounts.closure_2
  solana_pubkey.PubkeyError solana_program_error.ProgramError := {
  call_once :=
    r1_pool_adapter.owned.authenticate_asq8_accounts.closure_2.Insts.CoreOpsFunctionFnOnceTuplePubkeyErrorProgramError.call_once
}

def
  r1_pool_adapter.owned.authenticate_asq8_accounts.closure_1.Insts.CoreOpsFunctionFnOnceTuplePubkeyErrorProgramError.call_once
  (c : r1_pool_adapter.owned.authenticate_asq8_accounts.closure_1)
  (tupled_args : solana_pubkey.PubkeyError) :
  Result solana_program_error.ProgramError
  := do
  ok solana_program_error.ProgramError.InvalidAccountData

@[reducible]
def
  r1_pool_adapter.owned.authenticate_asq8_accounts.closure_1.Insts.CoreOpsFunctionFnOnceTuplePubkeyErrorProgramError
  : core.ops.function.FnOnce
  r1_pool_adapter.owned.authenticate_asq8_accounts.closure_1
  solana_pubkey.PubkeyError solana_program_error.ProgramError := {
  call_once :=
    r1_pool_adapter.owned.authenticate_asq8_accounts.closure_1.Insts.CoreOpsFunctionFnOnceTuplePubkeyErrorProgramError.call_once
}

def
  r1_pool_adapter.owned.authenticate_asq8_accounts.closure.Insts.CoreOpsFunctionFnOnceTuplePubkeyErrorProgramError.call_once
  (c : r1_pool_adapter.owned.authenticate_asq8_accounts.closure)
  (tupled_args : solana_pubkey.PubkeyError) :
  Result solana_program_error.ProgramError
  := do
  ok solana_program_error.ProgramError.InvalidAccountData

@[reducible]
def
  r1_pool_adapter.owned.authenticate_asq8_accounts.closure.Insts.CoreOpsFunctionFnOnceTuplePubkeyErrorProgramError
  : core.ops.function.FnOnce
  r1_pool_adapter.owned.authenticate_asq8_accounts.closure
  solana_pubkey.PubkeyError solana_program_error.ProgramError := {
  call_once :=
    r1_pool_adapter.owned.authenticate_asq8_accounts.closure.Insts.CoreOpsFunctionFnOnceTuplePubkeyErrorProgramError.call_once
}

def r1_pool_adapter.owned.authenticate_asq8_accounts (x : Ext)
  (verifier_program : solana_pubkey.Pubkey)
  (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
  (pool_program : solana_pubkey.Pubkey) (output_lane : Std.U8)
  (current_slot : Std.U64) :
  Result (core.result.Result r1_pool_adapter.AuthenticatedAsq8Accounts
    solana_program_error.ProgramError)
  := do
  let i := Slice.len accounts
  if i = 7#usize
  then
    let proof_account ← Slice.index_usize accounts 0#usize
    let master_account ← Slice.index_usize accounts 1#usize
    let checkpoint_account ← Slice.index_usize accounts 2#usize
    let lane_account ← Slice.index_usize accounts 3#usize
    let registry_account ← Slice.index_usize accounts 4#usize
    let entry_account ← Slice.index_usize accounts 5#usize
    let verifier_checkpoint ← Slice.index_usize accounts 6#usize
    let r ← x.r1_pool_adapter_owned_require_readonly_buffer proof_account
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let r1 ←
        x.r1_pool_adapter_owned_require_verifier_checkpoint verifier_checkpoint
          verifier_program false
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        let r2 ←
          x.r1_pool_adapter_owned_require_readonly_account master_account
            pool_program
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          let r3 ←
            x.r1_pool_adapter_owned_require_readonly_account checkpoint_account
              pool_program
          let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
          match cf3 with
          | core.ops.control_flow.ControlFlow.Continue _ =>
            let r4 ←
              x.r1_pool_adapter_owned_require_readonly_account lane_account
                pool_program
            let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r4
            match cf4 with
            | core.ops.control_flow.ControlFlow.Continue _ =>
              let r5 ←
                x.r1_pool_adapter_owned_require_distinct_accounts
                  (Array.make 7#usize [
                    proof_account, master_account, checkpoint_account,
                    lane_account, registry_account, entry_account,
                    verifier_checkpoint
                    ])
              let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r5
              match cf5 with
              | core.ops.control_flow.ControlFlow.Continue _ =>
                let r6 ←
                  (r1_pool_adapter.owned.OwnedAccount.data x) master_account
                let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r6
                match cf6 with
                | core.ops.control_flow.ControlFlow.Continue val =>
                  let r7 ← x.r1_pool_adapter_decode_master_box val
                  let cf7 ← core.result.Result.Insts.CoreOpsTry.branch r7
                  match cf7 with
                  | core.ops.control_flow.ControlFlow.Continue val1 =>
                    let p ←
                      r1_pool_adapter.owned.OwnedAccount.impl.key
                        master_account
                    let a ← x.solana_pubkey_Pubkey_to_bytes p
                    let b ←
                      core.array.equality.PartialEqArray.ne
                        core.cmp.PartialEqU8 val1.identity.pool a
                    if b
                    then
                      ok (core.result.Result.Err
                        solana_program_error.ProgramError.InvalidAccountData)
                    else
                      let i1 ←
                        x.aspis_statement_pool_v1_pair_forest_accounts_POOL_V1_PAIR_FOREST_ALL_LANES_MASK
                      if val1.initialized_lane_mask != i1
                      then
                        ok (core.result.Result.Err
                          solana_program_error.ProgramError.InvalidAccountData)
                      else
                        let p1 ←
                          x.solana_pubkey_Pubkey_new_from_array
                            val1.identity.asset_mint
                        let s ←
                          x.solana_pubkey_Pubkey_Insts_CoreConvertAsRefSliceU8_as_ref
                            p1
                        let s1 ←
                          lift (Array.to_slice
                            (Array.make 1#usize [ val1.bump ]))
                        let s2 ←
                          lift (Array.to_slice
                            (Array.make 3#usize [
                              r1_pool_adapter.PAIR_FOREST_MASTER_SEED, s, s1
                              ]))
                        let r8 ←
                          x.solana_pubkey_Pubkey_create_program_address s2
                            pool_program
                        let r9 ←
                          core.result.Result.map_err
                            r1_pool_adapter.owned.authenticate_asq8_accounts.closure.Insts.CoreOpsFunctionFnOnceTuplePubkeyErrorProgramError
                            r8 ()
                        let cf8 ←
                          core.result.Result.Insts.CoreOpsTry.branch r9
                        match cf8 with
                        | core.ops.control_flow.ControlFlow.Continue val2 =>
                          let b1 ←
                            core.cmp.PartialEq.ne.trait_default
                              (solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey x)
                              val2 p
                          if b1
                          then
                            ok (core.result.Result.Err
                              solana_program_error.ProgramError.InvalidAccountData)
                          else
                            let r10 ←
                              x.r1_pool_adapter_owned_authenticate_invariant_release_registry
                                verifier_program pool_program master_account
                                val1 registry_account entry_account
                                current_slot
                            let cf9 ←
                              core.result.Result.Insts.CoreOpsTry.branch r10
                            match cf9 with
                            | core.ops.control_flow.ControlFlow.Continue _ =>
                              let r11 ←
                                (r1_pool_adapter.owned.OwnedAccount.data x)
                                  checkpoint_account
                              let cf10 ←
                                core.result.Result.Insts.CoreOpsTry.branch r11
                              match cf10 with
                              | core.ops.control_flow.ControlFlow.Continue val3
                                =>
                                let r12 ←
                                  x.r1_pool_adapter_decode_checkpoint_box val3
                                let cf11 ←
                                  core.result.Result.Insts.CoreOpsTry.branch
                                    r12
                                match cf11 with
                                | core.ops.control_flow.ControlFlow.Continue
                                  val4 =>
                                  let a1 ← x.solana_pubkey_Pubkey_to_bytes p
                                  let b2 ←
                                    core.array.equality.PartialEqArray.ne
                                      core.cmp.PartialEqU8 val4.master a1
                                  if b2
                                  then
                                    ok (core.result.Result.Err
                                      solana_program_error.ProgramError.InvalidAccountData)
                                  else
                                    let b3 ←
                                      core.array.equality.PartialEqArray.ne
                                        core.cmp.PartialEqU8
                                        val4.deployment_domain
                                        val1.identity.deployment_domain
                                    if b3
                                    then
                                      ok (core.result.Result.Err
                                        solana_program_error.ProgramError.InvalidAccountData)
                                    else
                                      let s3 ←
                                        x.solana_pubkey_Pubkey_Insts_CoreConvertAsRefSliceU8_as_ref
                                          p
                                      let a2 ←
                                        lift (core.num.U64.to_le_bytes
                                          val4.checkpoint_sequence)
                                      let s4 ← lift (Array.to_slice a2)
                                      let s5 ←
                                        lift (Array.to_slice
                                          (Array.make 1#usize [ val4.bump ]))
                                      let s6 ←
                                        lift (Array.to_slice
                                          (Array.make 4#usize [
                                            r1_pool_adapter.PAIR_FOREST_CHECKPOINT_SEED,
                                            s3, s4, s5
                                            ]))
                                      let r13 ←
                                        x.solana_pubkey_Pubkey_create_program_address
                                          s6 pool_program
                                      let r14 ←
                                        core.result.Result.map_err
                                          r1_pool_adapter.owned.authenticate_asq8_accounts.closure_1.Insts.CoreOpsFunctionFnOnceTuplePubkeyErrorProgramError
                                          r13 ()
                                      let cf12 ←
                                        core.result.Result.Insts.CoreOpsTry.branch
                                          r14
                                      match cf12 with
                                      |
                                        core.ops.control_flow.ControlFlow.Continue
                                        val5 =>
                                        let p2 ←
                                          r1_pool_adapter.owned.OwnedAccount.impl.key
                                            checkpoint_account
                                        let b4 ←
                                          core.cmp.PartialEq.ne.trait_default
                                            (solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey x)
                                            val5 p2
                                        if b4
                                        then
                                          ok (core.result.Result.Err
                                            solana_program_error.ProgramError.InvalidAccountData)
                                        else
                                          let r15 ←
                                            (r1_pool_adapter.owned.OwnedAccount.data x)
                                              lane_account
                                          let cf13 ←
                                            core.result.Result.Insts.CoreOpsTry.branch
                                              r15
                                          match cf13 with
                                          |
                                            core.ops.control_flow.ControlFlow.Continue
                                            val6 =>
                                            let r16 ←
                                              x.r1_pool_adapter_decode_lane_from_pool_release
                                                val6
                                            let cf14 ←
                                              core.result.Result.Insts.CoreOpsTry.branch
                                                r16
                                            match cf14 with
                                            |
                                              core.ops.control_flow.ControlFlow.Continue
                                              val7 =>
                                              let a3 ←
                                                x.solana_pubkey_Pubkey_to_bytes p
                                              let b5 ←
                                                core.array.equality.PartialEqArray.ne
                                                  core.cmp.PartialEqU8
                                                  val7.master a3
                                              if b5
                                              then
                                                ok (core.result.Result.Err
                                                  solana_program_error.ProgramError.InvalidAccountData)
                                              else
                                                if val7.lane_id != output_lane
                                                then
                                                  ok (core.result.Result.Err
                                                    solana_program_error.ProgramError.InvalidAccountData)
                                                else
                                                  let s7 ←
                                                    x.solana_pubkey_Pubkey_Insts_CoreConvertAsRefSliceU8_as_ref
                                                      p
                                                  let s8 ←
                                                    lift (Array.to_slice
                                                      (Array.make 1#usize [
                                                        output_lane
                                                        ]))
                                                  let s9 ←
                                                    lift (Array.to_slice
                                                      (Array.make 1#usize [
                                                        val7.bump
                                                        ]))
                                                  let s10 ←
                                                    lift (Array.to_slice
                                                      (Array.make 4#usize [
                                                        r1_pool_adapter.PAIR_FOREST_LANE_SEED,
                                                        s7, s8, s9
                                                        ]))
                                                  let r17 ←
                                                    x.solana_pubkey_Pubkey_create_program_address
                                                      s10 pool_program
                                                  let r18 ←
                                                    core.result.Result.map_err
                                                      r1_pool_adapter.owned.authenticate_asq8_accounts.closure_2.Insts.CoreOpsFunctionFnOnceTuplePubkeyErrorProgramError
                                                      r17 ()
                                                  let cf15 ←
                                                    core.result.Result.Insts.CoreOpsTry.branch
                                                      r18
                                                  match cf15 with
                                                  |
                                                    core.ops.control_flow.ControlFlow.Continue
                                                    val8 =>
                                                    let p3 ←
                                                      r1_pool_adapter.owned.OwnedAccount.impl.key
                                                        lane_account
                                                    let b6 ←
                                                      core.cmp.PartialEq.ne.trait_default
                                                        (solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey x)
                                                        val8 p3
                                                    if b6
                                                    then
                                                      ok
                                                        (core.result.Result.Err
                                                        solana_program_error.ProgramError.InvalidAccountData)
                                                    else
                                                      let a4 ←
                                                        x.solana_pubkey_Pubkey_to_bytes
                                                          p
                                                      let a5 ←
                                                        x.solana_pubkey_Pubkey_to_bytes
                                                          p
                                                      let a6 ←
                                                        x.solana_pubkey_Pubkey_to_bytes
                                                          p2
                                                      let a7 ←
                                                        x.solana_pubkey_Pubkey_to_bytes
                                                          p3
                                                      ok (core.result.Result.Ok
                                                        {
                                                          master_account := a5,
                                                          checkpoint_account :=
                                                            a6,
                                                          selected_lane_account :=
                                                            a7,
                                                          master := val1,
                                                          checkpoint := val4,
                                                          selected_lane := val7,
                                                          live_snapshot :=
                                                            {
                                                              pool := a4,
                                                              deployment_domain :=
                                                                val1.identity.deployment_domain,
                                                              sequence :=
                                                                val7.tree.next_leaf_index,
                                                              next_pair_index :=
                                                                val7.tree.next_leaf_index,
                                                              current_root :=
                                                                val7.tree.root,
                                                              frontier :=
                                                                val7.tree.frontier
                                                            }
                                                        })
                                                  |
                                                    core.ops.control_flow.ControlFlow.Break
                                                    residual =>
                                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                      r1_pool_adapter.AuthenticatedAsq8Accounts
                                                      (core.convert.FromSame
                                                      solana_program_error.ProgramError)
                                                      residual
                                            |
                                              core.ops.control_flow.ControlFlow.Break
                                              residual =>
                                              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                r1_pool_adapter.AuthenticatedAsq8Accounts
                                                (core.convert.FromSame
                                                solana_program_error.ProgramError)
                                                residual
                                          |
                                            core.ops.control_flow.ControlFlow.Break
                                            residual =>
                                            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                              r1_pool_adapter.AuthenticatedAsq8Accounts
                                              (core.convert.FromSame
                                              solana_program_error.ProgramError)
                                              residual
                                      | core.ops.control_flow.ControlFlow.Break
                                        residual =>
                                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                          r1_pool_adapter.AuthenticatedAsq8Accounts
                                          (core.convert.FromSame
                                          solana_program_error.ProgramError)
                                          residual
                                | core.ops.control_flow.ControlFlow.Break
                                  residual =>
                                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                    r1_pool_adapter.AuthenticatedAsq8Accounts
                                    (core.convert.FromSame
                                    solana_program_error.ProgramError) residual
                              | core.ops.control_flow.ControlFlow.Break
                                residual =>
                                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                  r1_pool_adapter.AuthenticatedAsq8Accounts
                                  (core.convert.FromSame
                                  solana_program_error.ProgramError) residual
                            | core.ops.control_flow.ControlFlow.Break residual
                              =>
                              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                r1_pool_adapter.AuthenticatedAsq8Accounts
                                (core.convert.FromSame
                                solana_program_error.ProgramError) residual
                        | core.ops.control_flow.ControlFlow.Break residual =>
                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                            r1_pool_adapter.AuthenticatedAsq8Accounts
                            (core.convert.FromSame
                            solana_program_error.ProgramError) residual
                  | core.ops.control_flow.ControlFlow.Break residual =>
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                      r1_pool_adapter.AuthenticatedAsq8Accounts
                      (core.convert.FromSame solana_program_error.ProgramError)
                      residual
                | core.ops.control_flow.ControlFlow.Break residual =>
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                    r1_pool_adapter.AuthenticatedAsq8Accounts
                    (core.convert.FromSame solana_program_error.ProgramError)
                    residual
              | core.ops.control_flow.ControlFlow.Break residual =>
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                  r1_pool_adapter.AuthenticatedAsq8Accounts
                  (core.convert.FromSame solana_program_error.ProgramError)
                  residual
            | core.ops.control_flow.ControlFlow.Break residual =>
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                r1_pool_adapter.AuthenticatedAsq8Accounts
                (core.convert.FromSame solana_program_error.ProgramError)
                residual
          | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              r1_pool_adapter.AuthenticatedAsq8Accounts (core.convert.FromSame
              solana_program_error.ProgramError) residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            r1_pool_adapter.AuthenticatedAsq8Accounts (core.convert.FromSame
            solana_program_error.ProgramError) residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          r1_pool_adapter.AuthenticatedAsq8Accounts (core.convert.FromSame
          solana_program_error.ProgramError) residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        r1_pool_adapter.AuthenticatedAsq8Accounts (core.convert.FromSame
        solana_program_error.ProgramError) residual
  else
    let i1 := Slice.len accounts
    if i1 < 7#usize
    then
      ok (core.result.Result.Err
        solana_program_error.ProgramError.NotEnoughAccountKeys)
    else
      ok (core.result.Result.Err
        solana_program_error.ProgramError.InvalidArgument)

def
  r1_pool_adapter.owned.validate_asq8.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestAccountErrorV1ProgramError.call_once
  (c : r1_pool_adapter.owned.validate_asq8.closure_1)
  (tupled_args :
  aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1)
  :
  Result solana_program_error.ProgramError
  := do
  ok solana_program_error.ProgramError.InvalidInstructionData

@[reducible]
def
  r1_pool_adapter.owned.validate_asq8.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestAccountErrorV1ProgramError
  : core.ops.function.FnOnce r1_pool_adapter.owned.validate_asq8.closure_1
  aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1
  solana_program_error.ProgramError := {
  call_once :=
    r1_pool_adapter.owned.validate_asq8.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestAccountErrorV1ProgramError.call_once
}

def
  r1_pool_adapter.owned.validate_asq8.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError.call_once
  (c : r1_pool_adapter.owned.validate_asq8.closure)
  (tupled_args :
  aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
  :
  Result solana_program_error.ProgramError
  := do
  ok solana_program_error.ProgramError.InvalidInstructionData

@[reducible]
def
  r1_pool_adapter.owned.validate_asq8.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError
  : core.ops.function.FnOnce r1_pool_adapter.owned.validate_asq8.closure
  aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
  solana_program_error.ProgramError := {
  call_once :=
    r1_pool_adapter.owned.validate_asq8.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError.call_once
}

def r1_pool_adapter.owned.validate_asq8 (x : Ext)
  (verifier_program : solana_pubkey.Pubkey)
  (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
  (instruction_data : Slice Std.U8)
  (current_slot : core.result.Result Std.U64 solana_program_error.ProgramError)
  :
  Result (core.result.Result r1_pool_adapter.ValidatedAsqa
    solana_program_error.ProgramError)
  := do
  let i := Slice.len instruction_data
  let i1 ←
    x.aspis_statement_pool_v1_pair_forest_terminal_POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES
  if i != i1
  then
    ok (core.result.Result.Err
      solana_program_error.ProgramError.InvalidInstructionData)
  else
    let r ←
      x.aspis_statement_pool_v1_pair_forest_terminal_decode_pool_v1_pair_forest_terminal_request_v1
        instruction_data
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
          let a ← x.r1_pool_adapter_pool_program_id
          let b2 ←
            core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
              val.pool_program a
          if b2
          then
            ok (core.result.Result.Err
              solana_program_error.ProgramError.InvalidInstructionData)
          else
            let pool_program ←
              x.solana_pubkey_Pubkey_new_from_array val.pool_program
            let a1 ←
              x.aspis_statement_pool_v1_pair_forest_terminal_PoolV1PairForestTerminalPaymentV1_nullifier
                val.«public»
            let r2 ←
              x.aspis_statement_pool_v1_pair_forest_accounts_pool_v1_pair_forest_output_lane_v1
                a1
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
                  (r1_pool_adapter.owned.authenticate_asq8_accounts x)
                    verifier_program accounts pool_program val1 val2
                let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r4
                match cf3 with
                | core.ops.control_flow.ControlFlow.Continue val3 =>
                  let o ← x.core_slice_Slice_first accounts
                  let r5 ←
                    core.option.Option.ok_or o
                      solana_program_error.ProgramError.NotEnoughAccountKeys
                  let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r5
                  match cf4 with
                  | core.ops.control_flow.ControlFlow.Continue val4 =>
                    let r6 ← (r1_pool_adapter.owned.OwnedAccount.data x) val4
                    let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r6
                    match cf5 with
                    | core.ops.control_flow.ControlFlow.Continue val5 =>
                      let r7 ← x.r1_pool_adapter_scan_proof_buffer val5
                      let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r7
                      match cf6 with
                      | core.ops.control_flow.ControlFlow.Continue val6 =>
                        let r8 ←
                          x.r1_pool_adapter_reconstruct_asq8_statement val val3
                            val6.candidate_afterstate
                        let cf7 ←
                          core.result.Result.Insts.CoreOpsTry.branch r8
                        match cf7 with
                        | core.ops.control_flow.ControlFlow.Continue val7 =>
                          ok (core.result.Result.Ok
                            {
                              statement := val7,
                              proof_length := val6.proof_length
                            })
                        | core.ops.control_flow.ControlFlow.Break residual =>
                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                            r1_pool_adapter.ValidatedAsqa
                            (core.convert.FromSame
                            solana_program_error.ProgramError) residual
                      | core.ops.control_flow.ControlFlow.Break residual =>
                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                          r1_pool_adapter.ValidatedAsqa (core.convert.FromSame
                          solana_program_error.ProgramError) residual
                    | core.ops.control_flow.ControlFlow.Break residual =>
                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                        r1_pool_adapter.ValidatedAsqa (core.convert.FromSame
                        solana_program_error.ProgramError) residual
                  | core.ops.control_flow.ControlFlow.Break residual =>
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                      r1_pool_adapter.ValidatedAsqa (core.convert.FromSame
                      solana_program_error.ProgramError) residual
                | core.ops.control_flow.ControlFlow.Break residual =>
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                    r1_pool_adapter.ValidatedAsqa (core.convert.FromSame
                    solana_program_error.ProgramError) residual
              | core.ops.control_flow.ControlFlow.Break residual =>
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                  r1_pool_adapter.ValidatedAsqa (core.convert.FromSame
                  solana_program_error.ProgramError) residual
            | core.ops.control_flow.ControlFlow.Break residual =>
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                r1_pool_adapter.ValidatedAsqa (core.convert.FromSame
                solana_program_error.ProgramError) residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        r1_pool_adapter.ValidatedAsqa (core.convert.FromSame
        solana_program_error.ProgramError) residual

def
  r1_pool_adapter.owned.stage2_owned.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError.call_once
  (c : r1_pool_adapter.owned.stage2_owned.closure)
  (tupled_args :
  aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
  :
  Result solana_program_error.ProgramError
  := do
  ok solana_program_error.ProgramError.InvalidInstructionData

@[reducible]
def
  r1_pool_adapter.owned.stage2_owned.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError
  : core.ops.function.FnOnce r1_pool_adapter.owned.stage2_owned.closure
  aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
  solana_program_error.ProgramError := {
  call_once :=
    r1_pool_adapter.owned.stage2_owned.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError.call_once
}

def r1_pool_adapter.owned.stage2_owned (x : Ext)
  (program_id : solana_pubkey.Pubkey)
  (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (data : Slice Std.U8)
  (current_slot : core.result.Result Std.U64 solana_program_error.ProgramError)
  :
  Result (core.result.Result Unit solana_program_error.ProgramError)
  := do
  let i := Slice.len accounts
  if i != 7#usize
  then
    ok (core.result.Result.Err
      solana_program_error.ProgramError.InvalidInstructionData)
  else
    let o ←
      core.slice.Slice.get (core.slice.index.SliceIndexRangeToUsizeSlice
        Std.U8) data { «end» := 4#usize }
    let a ←
      x.aspis_statement_pool_v1_pair_forest_terminal_POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_MAGIC
    let s ←
      core.array.Array.index (core.ops.index.IndexSlice
        ((core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice x)
        Std.U8)) a ()
    let b ←
      core.cmp.PartialEq.ne.trait_default
        ((core.option.Option.Insts.CoreCmpPartialEqOption x)
        (core.cmp.PartialEqShared (Slice.Insts.CoreCmpPartialEqSlice
        core.cmp.PartialEqU8))) o (some s)
    if b
    then
      ok (core.result.Result.Err
        solana_program_error.ProgramError.InvalidInstructionData)
    else
      let r ←
        (r1_pool_adapter.owned.validate_asq8 x) program_id accounts data
          current_slot
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue val =>
        let oa ← Slice.index_usize accounts 0#usize
        let r1 ← (r1_pool_adapter.owned.OwnedAccount.data x) oa
        let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
        match cf1 with
        | core.ops.control_flow.ControlFlow.Continue val1 =>
          let oa1 ← Slice.index_usize accounts 6#usize
          let r2 ← (r1_pool_adapter.owned.OwnedAccount.data x) oa1
          let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
          match cf2 with
          | core.ops.control_flow.ControlFlow.Continue val2 =>
            let proof_start ←
              x.aspis_statement_pool_v1_pair_terminal_POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES
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
                ok (core.result.Result.Err
                  solana_program_error.ProgramError.InvalidAccountData)
              else
                let r4 ←
                  x.aspis_statement_pool_v1_pair_forest_terminal_encode_pool_v1_pair_forest_terminal_statement_v1
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
                    x.aspis_statement_pool_v1_pair_forest_terminal_POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES
                  if i2 != i3
                  then
                    ok (core.result.Result.Err
                      solana_program_error.ProgramError.InvalidInstructionData)
                  else
                    let s2 ← lift (Array.to_slice val4)
                    let s3 ←
                      core.slice.index.Slice.index
                        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)
                        val1 { start := proof_start, «end» := val3 }
                    let o2 ← x.observer
                    let r6 ←
                      x.aspis_r1_cost_probe_verifier_candidate_tx2_authenticated
                        (SolanaDigest.Insts.Aspis_coreDigestDigest32 x) s2 s3 val2
                        () o2
                    let r7 ←
                      core.result.Result.map_err (BuiltinFnOnce
                        aspis_r1_cost_probe.verifier.Error
                        solana_program_error.ProgramError) r6 (x.error)
                    let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r7
                    match cf5 with
                    | core.ops.control_flow.ControlFlow.Continue _ =>
                      x.r1_pool_adapter_emit_result val.statement
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

structure Bound (ops : Ops) (x : Ext) : Prop where
  h_aspis_statement_pool_v1_pair_forest_terminal_encode_pool_v1_pair_forest_terminal_statement_v1 : x.aspis_statement_pool_v1_pair_forest_terminal_encode_pool_v1_pair_forest_terminal_statement_v1 = ops.op22
  h_aspis_statement_pool_v1_pair_forest_terminal_decode_pool_v1_pair_forest_terminal_request_v1 : x.aspis_statement_pool_v1_pair_forest_terminal_decode_pool_v1_pair_forest_terminal_request_v1 = ops.op23
  h_aspis_statement_pool_v1_pair_forest_terminal_POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES : x.aspis_statement_pool_v1_pair_forest_terminal_POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES = AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES ops
  h_aspis_statement_pool_v1_pair_forest_terminal_PoolV1PairForestTerminalPaymentV1_nullifier : x.aspis_statement_pool_v1_pair_forest_terminal_PoolV1PairForestTerminalPaymentV1_nullifier = ops.op20
  h_aspis_statement_pool_v1_pair_forest_terminal_POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_MAGIC : x.aspis_statement_pool_v1_pair_forest_terminal_POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_MAGIC = ok (AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_MAGIC)
  h_aspis_statement_pool_v1_pair_forest_terminal_POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES : x.aspis_statement_pool_v1_pair_forest_terminal_POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES = AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES
  h_core_ops_range_RangeFull_Insts_CoreSliceIndexSliceIndexSliceSlice_get_unchecked_mut : @x.core_ops_range_RangeFull_Insts_CoreSliceIndexSliceIndexSliceSlice_get_unchecked_mut = @ops.op5
  h_core_ops_range_RangeFull_Insts_CoreSliceIndexSliceIndexSliceSlice_get_unchecked : @x.core_ops_range_RangeFull_Insts_CoreSliceIndexSliceIndexSliceSlice_get_unchecked = @ops.op6
  h_aspis_statement_pool_v1_pair_forest_accounts_POOL_V1_PAIR_FOREST_ALL_LANES_MASK : x.aspis_statement_pool_v1_pair_forest_accounts_POOL_V1_PAIR_FOREST_ALL_LANES_MASK = ops.op16
  h_aspis_statement_pool_v1_pair_forest_accounts_pool_v1_pair_forest_output_lane_v1 : x.aspis_statement_pool_v1_pair_forest_accounts_pool_v1_pair_forest_output_lane_v1 = ops.op17
  h_aspis_statement_pool_v1_pair_terminal_POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES : x.aspis_statement_pool_v1_pair_terminal_POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES = AdapterRw.aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES ops
  h_core_ops_range_RangeFull_Insts_CoreSliceIndexSliceIndexSliceSlice_index_mut : @x.core_ops_range_RangeFull_Insts_CoreSliceIndexSliceIndexSliceSlice_index_mut = @ops.op3
  h_core_ops_range_RangeFull_Insts_CoreSliceIndexSliceIndexSliceSlice_get_mut : @x.core_ops_range_RangeFull_Insts_CoreSliceIndexSliceIndexSliceSlice_get_mut = @ops.op7
  h_core_ops_range_RangeFull_Insts_CoreSliceIndexSliceIndexSliceSlice_index : @x.core_ops_range_RangeFull_Insts_CoreSliceIndexSliceIndexSliceSlice_index = @ops.op4
  h_core_ops_range_RangeFull_Insts_CoreSliceIndexSliceIndexSliceSlice_get : @x.core_ops_range_RangeFull_Insts_CoreSliceIndexSliceIndexSliceSlice_get = @ops.op8
  h_r1_pool_adapter_owned_authenticate_invariant_release_registry : x.r1_pool_adapter_owned_authenticate_invariant_release_registry = AdapterRw.r1_pool_adapter.owned.authenticate_invariant_release_registry ops
  h_solana_program_error_ProgramError_Insts_CoreCloneClone_clone : x.solana_program_error_ProgramError_Insts_CoreCloneClone_clone = ops.op35
  h_solana_pubkey_Pubkey_Insts_CoreConvertAsRefSliceU8_as_ref : x.solana_pubkey_Pubkey_Insts_CoreConvertAsRefSliceU8_as_ref = ops.op40
  h_aspis_r1_cost_probe_verifier_candidate_tx2_authenticated : @x.aspis_r1_cost_probe_verifier_candidate_tx2_authenticated = @ops.op11
  h_solana_pubkey_Pubkey_Insts_CoreCmpPartialEqPubkey_eq : x.solana_pubkey_Pubkey_Insts_CoreCmpPartialEqPubkey_eq = ops.op36
  h_core_option_Option_Insts_CoreCmpPartialEqOption_eq : @x.core_option_Option_Insts_CoreCmpPartialEqOption_eq = @ops.op2
  h_r1_pool_adapter_owned_require_verifier_checkpoint : x.r1_pool_adapter_owned_require_verifier_checkpoint = AdapterRw.r1_pool_adapter.owned.require_verifier_checkpoint ops
  h_r1_pool_adapter_owned_require_distinct_accounts : ∀ (N : Std.Usize), @x.r1_pool_adapter_owned_require_distinct_accounts N = @AdapterRw.r1_pool_adapter.owned.require_distinct_accounts ops N
  h_r1_pool_adapter_owned_require_readonly_account : x.r1_pool_adapter_owned_require_readonly_account = AdapterRw.r1_pool_adapter.owned.require_readonly_account ops
  h_r1_pool_adapter_decode_lane_from_pool_release : x.r1_pool_adapter_decode_lane_from_pool_release = ops.op50
  h_r1_pool_adapter_owned_require_readonly_buffer : x.r1_pool_adapter_owned_require_readonly_buffer = AdapterRw.r1_pool_adapter.owned.require_readonly_buffer
  h_solana_pubkey_Pubkey_create_program_address : x.solana_pubkey_Pubkey_create_program_address = ops.op38
  h_r1_pool_adapter_reconstruct_asq8_statement : x.r1_pool_adapter_reconstruct_asq8_statement = ops.op52
  h_r1_pool_adapter_decode_checkpoint_box : x.r1_pool_adapter_decode_checkpoint_box = ops.op49
  h_solana_pubkey_Pubkey_new_from_array : x.solana_pubkey_Pubkey_new_from_array = ops.op37
  h_r1_pool_adapter_decode_master_box : x.r1_pool_adapter_decode_master_box = ops.op48
  h_r1_pool_adapter_scan_proof_buffer : x.r1_pool_adapter_scan_proof_buffer = ops.op51
  h_r1_pool_adapter_pool_program_id : x.r1_pool_adapter_pool_program_id = ops.op45
  h_solana_pubkey_Pubkey_to_bytes : x.solana_pubkey_Pubkey_to_bytes = ops.op39
  h_r1_pool_adapter_emit_result : x.r1_pool_adapter_emit_result = ops.op53
  h_core_slice_Slice_first : @x.core_slice_Slice_first = @ops.op9
  h_observer : x.observer = AdapterRw.observer ops
  h_error : x.error = ops.op44
  h42 : ops.op42 = AdapterRw.PCVK_S2.SolanaDigest.Insts.CoreCloneClone.clone
  h43 : ops.op43 = AdapterRw.PCVK_S2.SolanaDigest.Insts.Aspis_coreDigestDigest32.digest x

end PCVK_S2
end AdapterRw

theorem PRVEq_partialEq_ne_default {Self Rhs : Type} (c : Self → Rhs → Result Bool) :
    ({ eq := c, ne := fun s o => core.cmp.PartialEq.ne.default c s o } : core.cmp.PartialEq Self Rhs) = { eq := c } := by
  have h : (fun s o => core.cmp.PartialEq.ne.default c s o) = core.cmp.PartialEq.ne._default c := by
    funext s o
    simp only [core.cmp.PartialEq.ne.default, core.cmp.PartialEq.ne._default, id]
    congr 1; funext b; cases b <;> rfl
  rw [h]; rfl

theorem PRVEq_usize_add_wrap (a b : Std.Usize) (h : a.val + b.val < 4294967296) :
    (a + b : Result Std.Usize) = ok (Std.Usize.wrapping_add a b) := by
  have hmax : a.val + b.val ≤ Std.Usize.max := by scalar_tac
  obtain ⟨z, hz, hv⟩ := Aeneas.Std.WP.spec_imp_exists (Usize.add_spec (x := a) (y := b) hmax)
  rw [hz]
  congr 1
  apply UScalar.eq_of_val_eq
  rw [hv, Std.Usize.wrapping_add_val_eq]
  have h2 : a.val + b.val < UScalar.size UScalarTy.Usize := by
    rw [Std.Usize.max_def] at hmax
    rw [UScalar.size_UScalarTyUsize, Std.Usize.size_def]
    have := Nat.one_le_two_pow (n := Std.Usize.numBits)
    omega
  exact (Nat.mod_eq_of_lt h2).symm

theorem PRVEq_after_ex (ops : AdapterRw.Ops) :
    ∃ ps : Std.Usize, AdapterRw.aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES ops = ok ps ∧ ps.val = 688 := by
  unfold AdapterRw.aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES AdapterRw.aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_PAYLOAD_BYTES
  have hmax : (8#usize).val + (680#usize).val ≤ Std.Usize.max := by scalar_tac
  obtain ⟨z, hz, hv⟩ := Aeneas.Std.WP.spec_imp_exists (Usize.add_spec (x := 8#usize) (y := 680#usize) hmax)
  refine ⟨z, hz, ?_⟩
  have h8 : (8#usize).val = 8 := by scalar_tac
  have h6 : (680#usize).val = 680 := by scalar_tac
  omega

namespace PRVEq.AdapterStage2_k1
variable {ops : AdapterRw.Ops} {x : AdapterRw.PCVK_S2.Ext} (b : AdapterRw.PCVK_S2.Bound ops x)
include b

theorem data_eq :
    AdapterRw.PCVK_S2.r1_pool_adapter.owned.OwnedAccount.data x = AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops := by
  funext self
  unfold AdapterRw.PCVK_S2.r1_pool_adapter.owned.OwnedAccount.data AdapterRw.r1_pool_adapter.owned.OwnedAccount.data
  rw [b.h_solana_program_error_ProgramError_Insts_CoreCloneClone_clone]
  rfl

theorem clone_inst_eq :
    AdapterRw.PCVK_S2.SolanaDigest.Insts.CoreCloneClone = AdapterRw.SolanaDigest.Insts.CoreCloneClone ops := by
  unfold AdapterRw.PCVK_S2.SolanaDigest.Insts.CoreCloneClone AdapterRw.SolanaDigest.Insts.CoreCloneClone
  rw [b.h42]

theorem copy_inst_eq :
    AdapterRw.PCVK_S2.SolanaDigest.Insts.CoreMarkerCopy = AdapterRw.SolanaDigest.Insts.CoreMarkerCopy ops := by
  unfold AdapterRw.PCVK_S2.SolanaDigest.Insts.CoreMarkerCopy AdapterRw.SolanaDigest.Insts.CoreMarkerCopy
  rw [clone_inst_eq b]

theorem digest_inst_eq :
    AdapterRw.PCVK_S2.SolanaDigest.Insts.Aspis_coreDigestDigest32 x = AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 ops := by
  unfold AdapterRw.PCVK_S2.SolanaDigest.Insts.Aspis_coreDigestDigest32 AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32
  rw [copy_inst_eq b, b.h43]

theorem pk_inst_eq :
    AdapterRw.PCVK_S2.solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey x = AdapterRw.solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey ops := by
  unfold AdapterRw.PCVK_S2.solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey AdapterRw.solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey
  rw [b.h_solana_pubkey_Pubkey_Insts_CoreCmpPartialEqPubkey_eq]

theorem opt_inst_eq (T : Type) (i : core.cmp.PartialEq T T) :
    @AdapterRw.PCVK_S2.core.option.Option.Insts.CoreCmpPartialEqOption x T i = @AdapterRw.core.option.Option.Insts.CoreCmpPartialEqOption ops T i := by
  unfold AdapterRw.PCVK_S2.core.option.Option.Insts.CoreCmpPartialEqOption AdapterRw.core.option.Option.Insts.CoreCmpPartialEqOption
  rw [b.h_core_option_Option_Insts_CoreCmpPartialEqOption_eq] <;> exact PRVEq_partialEq_ne_default _

theorem rf_inst_eq (T : Type) :
    @AdapterRw.PCVK_S2.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice x T = @AdapterRw.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice ops T := by
  unfold AdapterRw.PCVK_S2.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice AdapterRw.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice
  rw [b.h_core_ops_range_RangeFull_Insts_CoreSliceIndexSliceIndexSliceSlice_get, b.h_core_ops_range_RangeFull_Insts_CoreSliceIndexSliceIndexSliceSlice_get_mut, b.h_core_ops_range_RangeFull_Insts_CoreSliceIndexSliceIndexSliceSlice_get_unchecked, b.h_core_ops_range_RangeFull_Insts_CoreSliceIndexSliceIndexSliceSlice_get_unchecked_mut, b.h_core_ops_range_RangeFull_Insts_CoreSliceIndexSliceIndexSliceSlice_index, b.h_core_ops_range_RangeFull_Insts_CoreSliceIndexSliceIndexSliceSlice_index_mut]

theorem r1_pool_adapter_owned_authenticate_asq8_accounts_eq :
    AdapterRw.PCVK_S2.r1_pool_adapter.owned.authenticate_asq8_accounts x = AdapterRw.r1_pool_adapter.owned.authenticate_asq8_accounts ops := by
  funext verifier_program accounts pool_program output_lane current_slot
  unfold AdapterRw.PCVK_S2.r1_pool_adapter.owned.authenticate_asq8_accounts AdapterRw.r1_pool_adapter.owned.authenticate_asq8_accounts
  simp only [data_eq b, b.h_aspis_statement_pool_v1_pair_forest_terminal_encode_pool_v1_pair_forest_terminal_statement_v1, b.h_aspis_statement_pool_v1_pair_forest_terminal_decode_pool_v1_pair_forest_terminal_request_v1, b.h_aspis_statement_pool_v1_pair_forest_terminal_POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES, b.h_aspis_statement_pool_v1_pair_forest_terminal_PoolV1PairForestTerminalPaymentV1_nullifier, b.h_aspis_statement_pool_v1_pair_forest_terminal_POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_MAGIC, b.h_aspis_statement_pool_v1_pair_forest_terminal_POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES, b.h_core_ops_range_RangeFull_Insts_CoreSliceIndexSliceIndexSliceSlice_get_unchecked_mut, b.h_core_ops_range_RangeFull_Insts_CoreSliceIndexSliceIndexSliceSlice_get_unchecked, b.h_aspis_statement_pool_v1_pair_forest_accounts_POOL_V1_PAIR_FOREST_ALL_LANES_MASK, b.h_aspis_statement_pool_v1_pair_forest_accounts_pool_v1_pair_forest_output_lane_v1, b.h_aspis_statement_pool_v1_pair_terminal_POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES, b.h_core_ops_range_RangeFull_Insts_CoreSliceIndexSliceIndexSliceSlice_index_mut, b.h_core_ops_range_RangeFull_Insts_CoreSliceIndexSliceIndexSliceSlice_get_mut, b.h_core_ops_range_RangeFull_Insts_CoreSliceIndexSliceIndexSliceSlice_index, b.h_core_ops_range_RangeFull_Insts_CoreSliceIndexSliceIndexSliceSlice_get, b.h_r1_pool_adapter_owned_authenticate_invariant_release_registry, b.h_solana_program_error_ProgramError_Insts_CoreCloneClone_clone, b.h_solana_pubkey_Pubkey_Insts_CoreConvertAsRefSliceU8_as_ref, b.h_aspis_r1_cost_probe_verifier_candidate_tx2_authenticated, b.h_solana_pubkey_Pubkey_Insts_CoreCmpPartialEqPubkey_eq, b.h_core_option_Option_Insts_CoreCmpPartialEqOption_eq, b.h_r1_pool_adapter_owned_require_verifier_checkpoint, b.h_r1_pool_adapter_owned_require_distinct_accounts, b.h_r1_pool_adapter_owned_require_readonly_account, b.h_r1_pool_adapter_decode_lane_from_pool_release, b.h_r1_pool_adapter_owned_require_readonly_buffer, b.h_solana_pubkey_Pubkey_create_program_address, b.h_r1_pool_adapter_reconstruct_asq8_statement, b.h_r1_pool_adapter_decode_checkpoint_box, b.h_solana_pubkey_Pubkey_new_from_array, b.h_r1_pool_adapter_decode_master_box, b.h_r1_pool_adapter_scan_proof_buffer, b.h_r1_pool_adapter_pool_program_id, b.h_solana_pubkey_Pubkey_to_bytes, b.h_r1_pool_adapter_emit_result, b.h_core_slice_Slice_first, b.h_observer, b.h_error, rf_inst_eq b, digest_inst_eq b, opt_inst_eq b, pk_inst_eq b]
  rfl

theorem r1_pool_adapter_owned_stage2_owned_eq :
    AdapterRw.PCVK_S2.r1_pool_adapter.owned.stage2_owned x = AdapterRw.r1_pool_adapter.owned.stage2_owned ops := by
  funext program_id accounts data current_slot
  unfold AdapterRw.PCVK_S2.r1_pool_adapter.owned.stage2_owned AdapterRw.r1_pool_adapter.owned.stage2_owned
  simp only [data_eq b, r1_pool_adapter_owned_authenticate_asq8_accounts_eq b, b.h_aspis_statement_pool_v1_pair_forest_terminal_encode_pool_v1_pair_forest_terminal_statement_v1, b.h_aspis_statement_pool_v1_pair_forest_terminal_decode_pool_v1_pair_forest_terminal_request_v1, b.h_aspis_statement_pool_v1_pair_forest_terminal_POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES, b.h_aspis_statement_pool_v1_pair_forest_terminal_PoolV1PairForestTerminalPaymentV1_nullifier, b.h_aspis_statement_pool_v1_pair_forest_terminal_POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_MAGIC, b.h_aspis_statement_pool_v1_pair_forest_terminal_POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES, b.h_core_ops_range_RangeFull_Insts_CoreSliceIndexSliceIndexSliceSlice_get_unchecked_mut, b.h_core_ops_range_RangeFull_Insts_CoreSliceIndexSliceIndexSliceSlice_get_unchecked, b.h_aspis_statement_pool_v1_pair_forest_accounts_POOL_V1_PAIR_FOREST_ALL_LANES_MASK, b.h_aspis_statement_pool_v1_pair_forest_accounts_pool_v1_pair_forest_output_lane_v1, b.h_aspis_statement_pool_v1_pair_terminal_POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES, b.h_core_ops_range_RangeFull_Insts_CoreSliceIndexSliceIndexSliceSlice_index_mut, b.h_core_ops_range_RangeFull_Insts_CoreSliceIndexSliceIndexSliceSlice_get_mut, b.h_core_ops_range_RangeFull_Insts_CoreSliceIndexSliceIndexSliceSlice_index, b.h_core_ops_range_RangeFull_Insts_CoreSliceIndexSliceIndexSliceSlice_get, b.h_r1_pool_adapter_owned_authenticate_invariant_release_registry, b.h_solana_program_error_ProgramError_Insts_CoreCloneClone_clone, b.h_solana_pubkey_Pubkey_Insts_CoreConvertAsRefSliceU8_as_ref, b.h_aspis_r1_cost_probe_verifier_candidate_tx2_authenticated, b.h_solana_pubkey_Pubkey_Insts_CoreCmpPartialEqPubkey_eq, b.h_core_option_Option_Insts_CoreCmpPartialEqOption_eq, b.h_r1_pool_adapter_owned_require_verifier_checkpoint, b.h_r1_pool_adapter_owned_require_distinct_accounts, b.h_r1_pool_adapter_owned_require_readonly_account, b.h_r1_pool_adapter_decode_lane_from_pool_release, b.h_r1_pool_adapter_owned_require_readonly_buffer, b.h_solana_pubkey_Pubkey_create_program_address, b.h_r1_pool_adapter_reconstruct_asq8_statement, b.h_r1_pool_adapter_decode_checkpoint_box, b.h_solana_pubkey_Pubkey_new_from_array, b.h_r1_pool_adapter_decode_master_box, b.h_r1_pool_adapter_scan_proof_buffer, b.h_r1_pool_adapter_pool_program_id, b.h_solana_pubkey_Pubkey_to_bytes, b.h_r1_pool_adapter_emit_result, b.h_core_slice_Slice_first, b.h_observer, b.h_error, rf_inst_eq b, digest_inst_eq b, opt_inst_eq b, pk_inst_eq b]
  rfl

theorem r1_pool_adapter_owned_validate_asq8_eq :
    AdapterRw.PCVK_S2.r1_pool_adapter.owned.validate_asq8 x = AdapterRw.r1_pool_adapter.owned.validate_asq8 ops := by
  funext verifier_program accounts instruction_data current_slot
  unfold AdapterRw.PCVK_S2.r1_pool_adapter.owned.validate_asq8 AdapterRw.r1_pool_adapter.owned.validate_asq8
  simp only [data_eq b, r1_pool_adapter_owned_authenticate_asq8_accounts_eq b, r1_pool_adapter_owned_stage2_owned_eq b, b.h_aspis_statement_pool_v1_pair_forest_terminal_encode_pool_v1_pair_forest_terminal_statement_v1, b.h_aspis_statement_pool_v1_pair_forest_terminal_decode_pool_v1_pair_forest_terminal_request_v1, b.h_aspis_statement_pool_v1_pair_forest_terminal_POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES, b.h_aspis_statement_pool_v1_pair_forest_terminal_PoolV1PairForestTerminalPaymentV1_nullifier, b.h_aspis_statement_pool_v1_pair_forest_terminal_POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_MAGIC, b.h_aspis_statement_pool_v1_pair_forest_terminal_POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES, b.h_core_ops_range_RangeFull_Insts_CoreSliceIndexSliceIndexSliceSlice_get_unchecked_mut, b.h_core_ops_range_RangeFull_Insts_CoreSliceIndexSliceIndexSliceSlice_get_unchecked, b.h_aspis_statement_pool_v1_pair_forest_accounts_POOL_V1_PAIR_FOREST_ALL_LANES_MASK, b.h_aspis_statement_pool_v1_pair_forest_accounts_pool_v1_pair_forest_output_lane_v1, b.h_aspis_statement_pool_v1_pair_terminal_POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES, b.h_core_ops_range_RangeFull_Insts_CoreSliceIndexSliceIndexSliceSlice_index_mut, b.h_core_ops_range_RangeFull_Insts_CoreSliceIndexSliceIndexSliceSlice_get_mut, b.h_core_ops_range_RangeFull_Insts_CoreSliceIndexSliceIndexSliceSlice_index, b.h_core_ops_range_RangeFull_Insts_CoreSliceIndexSliceIndexSliceSlice_get, b.h_r1_pool_adapter_owned_authenticate_invariant_release_registry, b.h_solana_program_error_ProgramError_Insts_CoreCloneClone_clone, b.h_solana_pubkey_Pubkey_Insts_CoreConvertAsRefSliceU8_as_ref, b.h_aspis_r1_cost_probe_verifier_candidate_tx2_authenticated, b.h_solana_pubkey_Pubkey_Insts_CoreCmpPartialEqPubkey_eq, b.h_core_option_Option_Insts_CoreCmpPartialEqOption_eq, b.h_r1_pool_adapter_owned_require_verifier_checkpoint, b.h_r1_pool_adapter_owned_require_distinct_accounts, b.h_r1_pool_adapter_owned_require_readonly_account, b.h_r1_pool_adapter_decode_lane_from_pool_release, b.h_r1_pool_adapter_owned_require_readonly_buffer, b.h_solana_pubkey_Pubkey_create_program_address, b.h_r1_pool_adapter_reconstruct_asq8_statement, b.h_r1_pool_adapter_decode_checkpoint_box, b.h_solana_pubkey_Pubkey_new_from_array, b.h_r1_pool_adapter_decode_master_box, b.h_r1_pool_adapter_scan_proof_buffer, b.h_r1_pool_adapter_pool_program_id, b.h_solana_pubkey_Pubkey_to_bytes, b.h_r1_pool_adapter_emit_result, b.h_core_slice_Slice_first, b.h_observer, b.h_error, rf_inst_eq b, digest_inst_eq b, opt_inst_eq b, pk_inst_eq b]
  rfl

end PRVEq.AdapterStage2_k1

namespace PRVEq.AdapterStage2_k1
open AdapterRw AdapterRw.PCVK_S2
/-- Non-vacuity: for every ops0 there are ops (ops0 with the two digest fields set) and x with Bound ops x. -/
theorem bound_exists (ops0 : Ops) : ∃ ops : Ops, ∃ x : Ext, Bound ops x := by
  let ops : Ops := { ops0 with op42 := AdapterRw.PCVK_S2.SolanaDigest.Insts.CoreCloneClone.clone, op43 := fun _ _ => Result.fail Error.panic }
  exact ⟨ops, {
    Hash := Unit
    aspis_statement_pool_v1_pair_forest_terminal_encode_pool_v1_pair_forest_terminal_statement_v1 := ops.op22
    aspis_statement_pool_v1_pair_forest_terminal_decode_pool_v1_pair_forest_terminal_request_v1 := ops.op23
    aspis_statement_pool_v1_pair_forest_terminal_POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES := AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES ops
    aspis_statement_pool_v1_pair_forest_terminal_PoolV1PairForestTerminalPaymentV1_nullifier := ops.op20
    aspis_statement_pool_v1_pair_forest_terminal_POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_MAGIC := ok (AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_MAGIC)
    aspis_statement_pool_v1_pair_forest_terminal_POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES := AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES
    core_ops_range_RangeFull_Insts_CoreSliceIndexSliceIndexSliceSlice_get_unchecked_mut := @ops.op5
    core_ops_range_RangeFull_Insts_CoreSliceIndexSliceIndexSliceSlice_get_unchecked := @ops.op6
    aspis_statement_pool_v1_pair_forest_accounts_POOL_V1_PAIR_FOREST_ALL_LANES_MASK := ops.op16
    aspis_statement_pool_v1_pair_forest_accounts_pool_v1_pair_forest_output_lane_v1 := ops.op17
    aspis_statement_pool_v1_pair_terminal_POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES := AdapterRw.aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES ops
    core_ops_range_RangeFull_Insts_CoreSliceIndexSliceIndexSliceSlice_index_mut := @ops.op3
    core_ops_range_RangeFull_Insts_CoreSliceIndexSliceIndexSliceSlice_get_mut := @ops.op7
    core_ops_range_RangeFull_Insts_CoreSliceIndexSliceIndexSliceSlice_index := @ops.op4
    core_ops_range_RangeFull_Insts_CoreSliceIndexSliceIndexSliceSlice_get := @ops.op8
    r1_pool_adapter_owned_authenticate_invariant_release_registry := AdapterRw.r1_pool_adapter.owned.authenticate_invariant_release_registry ops
    solana_program_error_ProgramError_Insts_CoreCloneClone_clone := ops.op35
    solana_pubkey_Pubkey_Insts_CoreConvertAsRefSliceU8_as_ref := ops.op40
    aspis_r1_cost_probe_verifier_candidate_tx2_authenticated := @ops.op11
    solana_pubkey_Pubkey_Insts_CoreCmpPartialEqPubkey_eq := ops.op36
    core_option_Option_Insts_CoreCmpPartialEqOption_eq := @ops.op2
    r1_pool_adapter_owned_require_verifier_checkpoint := AdapterRw.r1_pool_adapter.owned.require_verifier_checkpoint ops
    r1_pool_adapter_owned_require_distinct_accounts := fun {N} => @AdapterRw.r1_pool_adapter.owned.require_distinct_accounts ops N
    r1_pool_adapter_owned_require_readonly_account := AdapterRw.r1_pool_adapter.owned.require_readonly_account ops
    r1_pool_adapter_decode_lane_from_pool_release := ops.op50
    r1_pool_adapter_owned_require_readonly_buffer := AdapterRw.r1_pool_adapter.owned.require_readonly_buffer
    solana_pubkey_Pubkey_create_program_address := ops.op38
    r1_pool_adapter_reconstruct_asq8_statement := ops.op52
    r1_pool_adapter_decode_checkpoint_box := ops.op49
    solana_pubkey_Pubkey_new_from_array := ops.op37
    r1_pool_adapter_decode_master_box := ops.op48
    r1_pool_adapter_scan_proof_buffer := ops.op51
    r1_pool_adapter_pool_program_id := ops.op45
    solana_pubkey_Pubkey_to_bytes := ops.op39
    r1_pool_adapter_emit_result := ops.op53
    solana_sha256_hasher_hashv := fun _ => Result.fail Error.panic
    solana_hash_Hash_to_bytes := fun _ => Result.fail Error.panic
    core_slice_Slice_first := @ops.op9
    observer := AdapterRw.observer ops
    error := ops.op44
    }, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
end PRVEq.AdapterStage2_k1

#print axioms PRVEq_partialEq_ne_default
#print axioms PRVEq_usize_add_wrap
#print axioms PRVEq_after_ex
#print axioms PRVEq.AdapterStage2_k1.data_eq
#print axioms PRVEq.AdapterStage2_k1.r1_pool_adapter_owned_authenticate_asq8_accounts_eq
#print axioms PRVEq.AdapterStage2_k1.r1_pool_adapter_owned_stage2_owned_eq
#print axioms PRVEq.AdapterStage2_k1.r1_pool_adapter_owned_validate_asq8_eq
#print axioms PRVEq.AdapterStage2_k1.digest_inst_eq
#print axioms PRVEq.AdapterStage2_k1.rf_inst_eq
#print axioms PRVEq.AdapterStage2_k1.bound_exists
