import R1Z.ProverRwRngNativeBodyLeaves
open Aeneas Aeneas.Std Result ControlFlow
noncomputable section
namespace ProverRwRngNativeBody
variable [TypeLeaves] [LocalLeaves]

/-- Trait implementation: [aspis_core::digest::{impl core::clone::Clone for aspis_core::digest::LegacyHashFn}]
    Source: 'crates/aspis-core/src/digest.rs', lines 12:9-12:14
    Name pattern: [core::clone::Clone<aspis_core::digest::LegacyHashFn>] -/
@[reducible, rust_trait_impl
  "core::clone::Clone<aspis_core::digest::LegacyHashFn>"]
def aspis_core.digest.LegacyHashFn.Insts.CoreCloneClone : core.clone.Clone
  aspis_core.digest.LegacyHashFn := {
  clone := aspis_core.digest.LegacyHashFn.Insts.CoreCloneClone.clone
}

/-- Trait implementation: [aspis_core::digest::{impl core::marker::Copy for aspis_core::digest::LegacyHashFn}]
    Source: 'crates/aspis-core/src/digest.rs', lines 12:16-12:20
    Name pattern: [core::marker::Copy<aspis_core::digest::LegacyHashFn>] -/
@[reducible, rust_trait_impl
  "core::marker::Copy<aspis_core::digest::LegacyHashFn>"]
def aspis_core.digest.LegacyHashFn.Insts.CoreMarkerCopy : core.marker.Copy
  aspis_core.digest.LegacyHashFn := {
  cloneInst := aspis_core.digest.LegacyHashFn.Insts.CoreCloneClone
}

/-- Trait implementation: [aspis_core::digest::{impl aspis_core::digest::Digest32 for aspis_core::digest::LegacyHashFn}]
    Source: 'crates/aspis-core/src/digest.rs', lines 15:0-15:30
    Name pattern: [aspis_core::digest::Digest32<aspis_core::digest::LegacyHashFn>] -/
@[reducible, rust_trait_impl
  "aspis_core::digest::Digest32<aspis_core::digest::LegacyHashFn>"]
def aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32 :
  aspis_core.digest.Digest32 aspis_core.digest.LegacyHashFn := {
  coremarkerCopyInst := aspis_core.digest.LegacyHashFn.Insts.CoreMarkerCopy
  digest :=
    aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32.digest
}

/-- Trait implementation: [aspis_core::field::wide_exact::{impl core::clone::Clone for aspis_core::field::wide_exact::WideExact}]
    Source: 'crates/aspis-core/src/field/wide_exact.rs', lines 27:9-27:14
    Name pattern: [core::clone::Clone<aspis_core::field::wide_exact::WideExact>] -/
@[reducible, rust_trait_impl
  "core::clone::Clone<aspis_core::field::wide_exact::WideExact>"]
def aspis_core.field.wide_exact.WideExact.Insts.CoreCloneClone :
  core.clone.Clone aspis_core.field.wide_exact.WideExact := {
  clone := aspis_core.field.wide_exact.WideExact.Insts.CoreCloneClone.clone
}

/-- Trait implementation: [aspis_core::field::{impl core::cmp::PartialEq<aspis_core::field::QM31> for aspis_core::field::QM31}]
    Source: 'crates/aspis-core/src/field.rs', lines 431:22-431:31
    Name pattern: [core::cmp::PartialEq<aspis_core::field::QM31, aspis_core::field::QM31>] -/
@[reducible, rust_trait_impl
  "core::cmp::PartialEq<aspis_core::field::QM31, aspis_core::field::QM31>"]
def aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 : core.cmp.PartialEq
  aspis_core.field.QM31 aspis_core.field.QM31 := {
  eq := aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq
  ne := core.cmp.PartialEq.ne.default
    aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq
}

/-- [aspis_core::state_only_hiding::PINNED_POOL_V1_PAIR_FOREST_RELATION_FREE_MASK_FINGERPRINT_V1]
    Source: 'crates/aspis-core/src/state_only_hiding.rs', lines 72:0-72:75
    Name pattern: [aspis_core::state_only_hiding::PINNED_POOL_V1_PAIR_FOREST_RELATION_FREE_MASK_FINGERPRINT_V1]
    Visibility: public -/
@[global_simps, irreducible, rust_const
  "aspis_core::state_only_hiding::PINNED_POOL_V1_PAIR_FOREST_RELATION_FREE_MASK_FINGERPRINT_V1"]
def
  aspis_core.state_only_hiding.PINNED_POOL_V1_PAIR_FOREST_RELATION_FREE_MASK_FINGERPRINT_V1
  : Std.U64 :=
  18003970557850322385#u64

/-- [aspis_core::state_only_hiding::PINNED_POOL_V1_PAIR_FOREST_HIDING_LAYOUT_FACTOR_FINGERPRINT_V1]
    Source: 'crates/aspis-core/src/state_only_hiding.rs', lines 76:0-76:77
    Name pattern: [aspis_core::state_only_hiding::PINNED_POOL_V1_PAIR_FOREST_HIDING_LAYOUT_FACTOR_FINGERPRINT_V1]
    Visibility: public -/
@[global_simps, irreducible, rust_const
  "aspis_core::state_only_hiding::PINNED_POOL_V1_PAIR_FOREST_HIDING_LAYOUT_FACTOR_FINGERPRINT_V1"]
def
  aspis_core.state_only_hiding.PINNED_POOL_V1_PAIR_FOREST_HIDING_LAYOUT_FACTOR_FINGERPRINT_V1
  : Std.U64 :=
  7605398817818846427#u64

/-- [aspis_core::state_only_hiding::{aspis_core::state_only_hiding::StateOnlyHidingContext}::pool_v1_pair_forest_v1]:
    Source: 'crates/aspis-core/src/state_only_hiding.rs', lines 153:4-153:97
    Name pattern: [aspis_core::state_only_hiding::{aspis_core::state_only_hiding::StateOnlyHidingContext}::pool_v1_pair_forest_v1]
    Visibility: public -/
@[rust_fun
  "aspis_core::state_only_hiding::{aspis_core::state_only_hiding::StateOnlyHidingContext}::pool_v1_pair_forest_v1"]
def aspis_core.state_only_hiding.StateOnlyHidingContext.pool_v1_pair_forest_v1
  (statement_digest : Array Std.U8 32#usize)
  (mask_nonce : Array Std.U8 32#usize) :
  Result aspis_core.state_only_hiding.StateOnlyHidingContext
  := do
  ok
    {
      statement_digest,
      mask_nonce,
      mask_layout_fingerprint :=
        aspis_core.state_only_hiding.PINNED_POOL_V1_PAIR_FOREST_RELATION_FREE_MASK_FINGERPRINT_V1,
      layout_factor_fingerprint :=
        aspis_core.state_only_hiding.PINNED_POOL_V1_PAIR_FOREST_HIDING_LAYOUT_FACTOR_FINGERPRINT_V1
    }

/-- [aspis_core::state_only_hiding::{aspis_core::state_only_hiding::StateOnlyHidingContext}::encode]:
    Source: 'crates/aspis-core/src/state_only_hiding.rs', lines 175:4-175:64
    Name pattern: [aspis_core::state_only_hiding::{aspis_core::state_only_hiding::StateOnlyHidingContext}::encode]
    Visibility: public -/
@[rust_fun
  "aspis_core::state_only_hiding::{aspis_core::state_only_hiding::StateOnlyHidingContext}::encode"]
def aspis_core.state_only_hiding.StateOnlyHidingContext.encode
  (self : aspis_core.state_only_hiding.StateOnlyHidingContext) :
  Result (Array Std.U8 81#usize)
  := do
  let encoded := Array.repeat 81#usize 0#u8
  let i ← aspis_core.state_only_hiding.STATE_ONLY_HIDING_CONTEXT_VERSION
  let encoded1 ← Array.update encoded 0#usize i
  let (s, index_mut_back) ←
    core.array.Array.index_mut (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) encoded1
      { start := 1#usize, «end» := 33#usize }
  let s1 ← lift (Array.to_slice self.statement_digest)
  let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
  let encoded2 := index_mut_back s2
  let (s3, index_mut_back1) ←
    core.array.Array.index_mut (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) encoded2
      { start := 33#usize, «end» := 65#usize }
  let s4 ← lift (Array.to_slice self.mask_nonce)
  let s5 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s3 s4
  let encoded3 := index_mut_back1 s5
  let (s6, index_mut_back2) ←
    core.array.Array.index_mut (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) encoded3
      { start := 65#usize, «end» := 73#usize }
  let a ← lift (core.num.U64.to_le_bytes self.mask_layout_fingerprint)
  let s7 ← lift (Array.to_slice a)
  let s8 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s6 s7
  let encoded4 := index_mut_back2 s8
  let (s9, index_mut_back3) ←
    core.array.Array.index_mut (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) encoded4
      { start := 73#usize, «end» := 81#usize }
  let a1 ← lift (core.num.U64.to_le_bytes self.layout_factor_fingerprint)
  let s10 ← lift (Array.to_slice a1)
  let s11 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s9 s10
  ok (index_mut_back3 s11)

/-- [aspis_prover::state_only_entropy::POOL_V1_SOURCE_SEED_DOMAIN]
    Source: 'crates/aspis-prover/src/state_only_entropy.rs', lines 62:0-62:39
    Name pattern: [aspis_prover::state_only_entropy::POOL_V1_SOURCE_SEED_DOMAIN] -/
@[global_simps, irreducible, rust_const
  "aspis_prover::state_only_entropy::POOL_V1_SOURCE_SEED_DOMAIN"]
def aspis_prover.state_only_entropy.POOL_V1_SOURCE_SEED_DOMAIN
  : Slice Std.U8 :=
  Array.to_slice
    (Array.make 39#usize [
      97#u8, 115#u8, 112#u8, 105#u8, 115#u8, 58#u8, 115#u8, 116#u8, 97#u8,
      116#u8, 101#u8, 45#u8, 111#u8, 110#u8, 108#u8, 121#u8, 58#u8, 112#u8,
      111#u8, 111#u8, 108#u8, 45#u8, 118#u8, 49#u8, 58#u8, 115#u8, 111#u8,
      117#u8, 114#u8, 99#u8, 101#u8, 45#u8, 115#u8, 101#u8, 101#u8, 100#u8,
      58#u8, 118#u8, 49#u8
      ])

/-- Trait implementation: [zeroize::{impl zeroize::Zeroize for [Z; N]}]
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/zeroize-1.8.1/src/lib.rs', lines 369:0-371:15
    Name pattern: [zeroize::Zeroize<[@Z; @N]>] -/
@[reducible, rust_trait_impl "zeroize::Zeroize<[@Z; @N]>"]
def Array.Insts.ZeroizeZeroize {Z : Type} (N : Std.Usize) (ZeroizeInst :
  zeroize.Zeroize Z) : zeroize.Zeroize (Array Z N) := {
  zeroize := Array.Insts.ZeroizeZeroize.zeroize ZeroizeInst
}

/-- Trait implementation: [zeroize::{impl zeroize::DefaultIsZeroes for u8}]
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/zeroize-1.8.1/src/lib.rs', lines 309:10-309:40
    Name pattern: [zeroize::DefaultIsZeroes<u8>] -/
@[reducible, rust_trait_impl "zeroize::DefaultIsZeroes<u8>"]
def U8.Insts.ZeroizeDefaultIsZeroes : zeroize.DefaultIsZeroes Std.U8 := {
  coremarkerCopyInst := core.marker.CopyU8
  coredefaultDefaultInst := core.default.DefaultU8
}

/-- Trait implementation: [zeroize::{impl zeroize::Zeroize for Z}]
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/zeroize-1.8.1/src/lib.rs', lines 297:0-299:23
    Name pattern: [zeroize::Zeroize<@Z>] -/
@[reducible, rust_trait_impl "zeroize::Zeroize<@Z>"]
def zeroize.Zeroize.Blanket {Z : Type} (DefaultIsZeroesInst :
  zeroize.DefaultIsZeroes Z) : zeroize.Zeroize Z := {
  zeroize := zeroize.Zeroize.Blanket.zeroize DefaultIsZeroesInst
}

/-- [aspis_prover::state_only_entropy::{aspis_prover::state_only_entropy::StateOnlyAttemptSecrets}::mask_nonce]:
    Source: 'crates/aspis-prover/src/state_only_entropy.rs', lines 240:4-240:40
    Name pattern: [aspis_prover::state_only_entropy::{aspis_prover::state_only_entropy::StateOnlyAttemptSecrets}::mask_nonce]
    Visibility: public -/
@[rust_fun
  "aspis_prover::state_only_entropy::{aspis_prover::state_only_entropy::StateOnlyAttemptSecrets}::mask_nonce"]
def aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.impl.mask_nonce
  (self : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets) :
  Result (Array Std.U8 32#usize)
  := do
  ok self.mask_nonce

/-- [aspis_prover::state_only_entropy::{impl aspis_prover::state_only_hiding::StateOnlyMaskNonceStore for aspis_prover::state_only_entropy::PreReservedNonce}::reserve]:
    Source: 'crates/aspis-prover/src/state_only_entropy.rs', lines 466:4-466:83
    Name pattern: [aspis_prover::state_only_entropy::{aspis_prover::state_only_hiding::StateOnlyMaskNonceStore<aspis_prover::state_only_entropy::PreReservedNonce>}::reserve]
    Visibility: public -/
@[rust_fun
  "aspis_prover::state_only_entropy::{aspis_prover::state_only_hiding::StateOnlyMaskNonceStore<aspis_prover::state_only_entropy::PreReservedNonce>}::reserve"]
def
  aspis_prover.state_only_entropy.PreReservedNonce.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore.reserve
  (self : aspis_prover.state_only_entropy.PreReservedNonce)
  (statement_digest : Array Std.U8 32#usize)
  (mask_nonce : Array Std.U8 32#usize) :
  Result (Bool × aspis_prover.state_only_entropy.PreReservedNonce)
  := do
  if self.consumed
  then ok (false, self)
  else
    let b ←
      core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
        statement_digest self.statement_digest
    if b
    then ok (false, self)
    else
      let b1 ←
        core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 mask_nonce
          self.mask_nonce
      if b1
      then ok (false, self)
      else ok (true, { self with consumed := true })

/-- Trait implementation: [aspis_prover::state_only_entropy::{impl aspis_prover::state_only_hiding::StateOnlyMaskNonceStore for aspis_prover::state_only_entropy::PreReservedNonce}]
    Source: 'crates/aspis-prover/src/state_only_entropy.rs', lines 465:0-465:49
    Name pattern: [aspis_prover::state_only_hiding::StateOnlyMaskNonceStore<aspis_prover::state_only_entropy::PreReservedNonce>] -/
@[reducible, rust_trait_impl
  "aspis_prover::state_only_hiding::StateOnlyMaskNonceStore<aspis_prover::state_only_entropy::PreReservedNonce>"]
def
  aspis_prover.state_only_entropy.PreReservedNonce.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore
  : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore
  aspis_prover.state_only_entropy.PreReservedNonce := {
  «reserve» :=
    aspis_prover.state_only_entropy.PreReservedNonce.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore.reserve
}

/-- [aspis_prover::state_only_entropy::{aspis_prover::state_only_entropy::StateOnlyAttemptSecrets}::reserve_and_build_pool_v1_pair_forest_mask_material_v1]:
    Source: 'crates/aspis-prover/src/state_only_entropy.rs', lines 405:4-411:98
    Name pattern: [aspis_prover::state_only_entropy::{aspis_prover::state_only_entropy::StateOnlyAttemptSecrets}::reserve_and_build_pool_v1_pair_forest_mask_material_v1]
    Visibility: public -/
@[rust_fun
  "aspis_prover::state_only_entropy::{aspis_prover::state_only_entropy::StateOnlyAttemptSecrets}::reserve_and_build_pool_v1_pair_forest_mask_material_v1"]
def
  aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.reserve_and_build_pool_v1_pair_forest_mask_material_v1
  {T0 : Type} (state_only_hidingStateOnlyMaskNonceStoreInst :
  aspis_prover.state_only_hiding.StateOnlyMaskNonceStore T0)
  (self : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (precommit_binding : Array Std.U8 32#usize)
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
  (nonce_store : T0) :
  Result ((core.result.Result
    (aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets ×
    aspis_prover.state_only_hiding.StateOnlyMaskMaterial)
    aspis_prover.state_only_hiding.StateOnlyMaskBuildError) × T0)
  := do
  let b ←
    core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
      context.mask_nonce self.mask_nonce
  if b
  then
    ok (core.result.Result.Err
      aspis_prover.state_only_hiding.StateOnlyMaskBuildError.Layout,
      nonce_store)
  else
    if context.mask_layout_fingerprint !=
      aspis_core.state_only_hiding.PINNED_POOL_V1_PAIR_FOREST_RELATION_FREE_MASK_FINGERPRINT_V1
    then
      ok (core.result.Result.Err
        aspis_prover.state_only_hiding.StateOnlyMaskBuildError.Layout,
        nonce_store)
    else
      if context.layout_factor_fingerprint !=
        aspis_core.state_only_hiding.PINNED_POOL_V1_PAIR_FOREST_HIDING_LAYOUT_FACTOR_FINGERPRINT_V1
      then
        ok (core.result.Result.Err
          aspis_prover.state_only_hiding.StateOnlyMaskBuildError.Layout,
          nonce_store)
      else
        let (b1, nonce_store1) ←
          state_only_hidingStateOnlyMaskNonceStoreInst.«reserve» nonce_store
            context.statement_digest context.mask_nonce
        if b1
        then
          let a ←
            zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
              (Array.Insts.ZeroizeZeroize 32#usize (zeroize.Zeroize.Blanket
              U8.Insts.ZeroizeDefaultIsZeroes)) self.field_mask_entropy
          let (r, pre_reserved) ←
            aspis_prover.state_only_hiding.build_pool_v1_pair_forest_mask_material_v1_from_entropy_ref
              aspis_prover.state_only_entropy.PreReservedNonce.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore
              hash precommit_binding context a
              {
                statement_digest := context.statement_digest,
                mask_nonce := context.mask_nonce,
                consumed := false
              }
          let cf ← core.result.Result.Insts.CoreOpsTry.branch r
          match cf with
          | core.ops.control_flow.ControlFlow.Continue val =>
            if pre_reserved.consumed
            then
              let s ← lift (Array.to_slice precommit_binding)
              let a1 ←
                aspis_core.state_only_hiding.StateOnlyHidingContext.encode
                  context
              let s1 ← lift (Array.to_slice a1)
              let s2 ←
                zeroize.Zeroizing.Insts.CoreConvertAsRef.as_ref
                  (Array.Insts.CoreConvertAsRefSlice Std.U8 32#usize)
                  (Array.Insts.ZeroizeZeroize 32#usize (zeroize.Zeroize.Blanket
                  U8.Insts.ZeroizeDefaultIsZeroes)) self.field_mask_entropy
              let s3 ←
                lift (Array.to_slice
                  (Array.make 4#usize [
                    aspis_prover.state_only_entropy.POOL_V1_SOURCE_SEED_DOMAIN,
                    s, s1, s2
                    ]))
              let a2 ← hash s3
              let source_mask_seed ←
                zeroize.Zeroizing.new (Array.Insts.ZeroizeZeroize 32#usize
                  (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) a2
              let _ ←
                zeroize.Zeroizing.Insts.ZeroizeZeroize.zeroize
                  (Array.Insts.ZeroizeZeroize 32#usize (zeroize.Zeroize.Blanket
                  U8.Insts.ZeroizeDefaultIsZeroes)) self.field_mask_entropy
              ok (core.result.Result.Ok
                ({
                   mask_nonce := self.mask_nonce,
                   precommit_binding,
                   reserved_context := context,
                   leaf_salt_seed := self.leaf_salt_seed,
                   source_mask_seed
                 }, val), nonce_store1)
            else
              ok (core.result.Result.Err
                aspis_prover.state_only_hiding.StateOnlyMaskBuildError.ReusedMaskNonce,
                nonce_store1)
          | core.ops.control_flow.ControlFlow.Break residual =>
            let r1 ←
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                (aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets
                × aspis_prover.state_only_hiding.StateOnlyMaskMaterial)
                (core.convert.FromSame
                aspis_prover.state_only_hiding.StateOnlyMaskBuildError)
                residual
            ok (r1, nonce_store1)
        else
          ok (core.result.Result.Err
            aspis_prover.state_only_hiding.StateOnlyMaskBuildError.ReusedMaskNonce,
            nonce_store1)

/-- [aspis_prover::state_only_entropy::{impl aspis_prover::state_only_hiding::StateOnlyMaskNonceStore for aspis_prover::state_only_entropy::DurableStateOnlyMaskNonceStore}::reserve]:
    Source: 'crates/aspis-prover/src/state_only_entropy.rs', lines 1003:4-1003:83
    Name pattern: [aspis_prover::state_only_entropy::{aspis_prover::state_only_hiding::StateOnlyMaskNonceStore<aspis_prover::state_only_entropy::DurableStateOnlyMaskNonceStore>}::reserve]
    Visibility: public -/
@[rust_fun
  "aspis_prover::state_only_entropy::{aspis_prover::state_only_hiding::StateOnlyMaskNonceStore<aspis_prover::state_only_entropy::DurableStateOnlyMaskNonceStore>}::reserve"]
def
  aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore.reserve
  (self : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore)
  (statement_digest : Array Std.U8 32#usize)
  (mask_nonce : Array Std.U8 32#usize) :
  Result (Bool ×
    aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore)
  := do
  let (r, self1) ←
    aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reserve_fallible
      self statement_digest mask_nonce
  match r with
  | core.result.Result.Ok reserved => ok (reserved, self1)
  | core.result.Result.Err error =>
    let ek ← std.io.error.Error.kind error
    ok (false, { self1 with last_error := (some ek) })

/-- Trait implementation: [aspis_prover::state_only_entropy::{impl aspis_prover::state_only_hiding::StateOnlyMaskNonceStore for aspis_prover::state_only_entropy::DurableStateOnlyMaskNonceStore}]
    Source: 'crates/aspis-prover/src/state_only_entropy.rs', lines 1002:0-1002:63
    Name pattern: [aspis_prover::state_only_hiding::StateOnlyMaskNonceStore<aspis_prover::state_only_entropy::DurableStateOnlyMaskNonceStore>] -/
@[reducible, rust_trait_impl
  "aspis_prover::state_only_hiding::StateOnlyMaskNonceStore<aspis_prover::state_only_entropy::DurableStateOnlyMaskNonceStore>"]
def
  aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore
  : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore
  aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore := {
  «reserve» :=
    aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore.reserve
}

/-- [aspis_prover::state_only_hiding::{impl core::cmp::PartialEq<aspis_prover::state_only_hiding::StateOnlyMaskBuildError> for aspis_prover::state_only_hiding::StateOnlyMaskBuildError}::eq]:
    Source: 'crates/aspis-prover/src/state_only_hiding.rs', lines 50:29-50:38
    Name pattern: [aspis_prover::state_only_hiding::{core::cmp::PartialEq<aspis_prover::state_only_hiding::StateOnlyMaskBuildError, aspis_prover::state_only_hiding::StateOnlyMaskBuildError>}::eq]
    Visibility: public -/
@[rust_fun
  "aspis_prover::state_only_hiding::{core::cmp::PartialEq<aspis_prover::state_only_hiding::StateOnlyMaskBuildError, aspis_prover::state_only_hiding::StateOnlyMaskBuildError>}::eq"]
def
  aspis_prover.state_only_hiding.StateOnlyMaskBuildError.Insts.CoreCmpPartialEqStateOnlyMaskBuildError.eq
  (self : aspis_prover.state_only_hiding.StateOnlyMaskBuildError)
  (other : aspis_prover.state_only_hiding.StateOnlyMaskBuildError) :
  Result Bool
  := do
  let self1 := read_discriminant self
  let other1 := read_discriminant other
  ok (self1 = other1)

/-- Trait implementation: [aspis_r1_cost_probe::prover::{impl aspis_r1_cost_probe::host_semantic::Commitments for aspis_r1_cost_probe::prover::Backend}]
    Source: 'crates/aspis-r1-cost-probe/src/prover.rs', lines 11:0-36:1 -/
@[reducible]
def prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments :
  host_semantic.Commitments prover.Backend := {
  c1 := prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1
  c2 := prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2
}

/-- [aspis_r1_cost_probe::transport::{aspis_r1_cost_probe::transport::Variant}::tag]:
    Source: 'crates/aspis-r1-cost-probe/src/transport.rs', lines 6:4-6:80
    Visibility: public -/
def transport.Variant.tag (self : transport.Variant) : Result Std.U8 := do
  match self with
  | transport.Variant.S1 => ok 1#u8
  | transport.Variant.S2 => ok 2#u8
  | transport.Variant.D => ok 3#u8

/-- [aspis_r1_cost_probe::prover::mask_error]:
    Source: 'crates/aspis-r1-cost-probe/src/prover.rs', lines 256:0-261:1 -/
def prover.mask_error
  (e : aspis_prover.state_only_hiding.StateOnlyMaskBuildError) :
  Result verifier.Error
  := do
  let b ←
    aspis_prover.state_only_hiding.StateOnlyMaskBuildError.Insts.CoreCmpPartialEqStateOnlyMaskBuildError.eq
      e
      aspis_prover.state_only_hiding.StateOnlyMaskBuildError.MaskSampleExhausted
  if b
  then ok verifier.Error.Rejected
  else ok verifier.Error.Semantic

/-- [aspis_r1_cost_probe::prover::prove_masked_with_attempt::{impl core::ops::function::FnOnce<(aspis_core::r0::Error,), aspis_r1_cost_probe::verifier::Error> for aspis_r1_cost_probe::prover::prove_masked_with_attempt::closure#3<T0>}::call_once]:
    Source: 'crates/aspis-r1-cost-probe/src/prover.rs', lines 211:78-211:98 -/
def
  prover.prove_masked_with_attempt.closure_3.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once
  {T0 : Type} (aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst :
  aspis_prover.state_only_hiding.StateOnlyMaskNonceStore T0)
  (c : prover.prove_masked_with_attempt.closure_3 T0)
  (tupled_args : aspis_core.r0.Error) :
  Result verifier.Error
  := do
  ok verifier.Error.Allocation

/-- Trait implementation: [aspis_r1_cost_probe::prover::prove_masked_with_attempt::{impl core::ops::function::FnOnce<(aspis_core::r0::Error,), aspis_r1_cost_probe::verifier::Error> for aspis_r1_cost_probe::prover::prove_masked_with_attempt::closure#3<T0>}]
    Source: 'crates/aspis-r1-cost-probe/src/prover.rs', lines 211:78-211:98 -/
@[reducible]
def
  prover.prove_masked_with_attempt.closure_3.Insts.CoreOpsFunctionFnOnceTupleErrorError
  {T0 : Type} (aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst :
  aspis_prover.state_only_hiding.StateOnlyMaskNonceStore T0) :
  core.ops.function.FnOnce (prover.prove_masked_with_attempt.closure_3 T0)
  aspis_core.r0.Error verifier.Error := {
  call_once :=
    prover.prove_masked_with_attempt.closure_3.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once
    aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst
}

/-- [aspis_r1_cost_probe::prover::prove_masked_with_attempt::{impl core::ops::function::FnOnce<(alloc::vec::Vec<aspis_core::field::QM31>,), aspis_r1_cost_probe::verifier::Error> for aspis_r1_cost_probe::prover::prove_masked_with_attempt::closure#2<T0>}::call_once]:
    Source: 'crates/aspis-r1-cost-probe/src/prover.rs', lines 197:124-197:142 -/
def
  prover.prove_masked_with_attempt.closure_2.Insts.CoreOpsFunctionFnOnceTupleVecQM31Error.call_once
  {T0 : Type} (aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst :
  aspis_prover.state_only_hiding.StateOnlyMaskNonceStore T0)
  (c : prover.prove_masked_with_attempt.closure_2 T0)
  (tupled_args : alloc.vec.Vec aspis_core.field.QM31) :
  Result verifier.Error
  := do
  ok verifier.Error.Semantic

/-- Trait implementation: [aspis_r1_cost_probe::prover::prove_masked_with_attempt::{impl core::ops::function::FnOnce<(alloc::vec::Vec<aspis_core::field::QM31>,), aspis_r1_cost_probe::verifier::Error> for aspis_r1_cost_probe::prover::prove_masked_with_attempt::closure#2<T0>}]
    Source: 'crates/aspis-r1-cost-probe/src/prover.rs', lines 197:124-197:142 -/
@[reducible]
def
  prover.prove_masked_with_attempt.closure_2.Insts.CoreOpsFunctionFnOnceTupleVecQM31Error
  {T0 : Type} (aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst :
  aspis_prover.state_only_hiding.StateOnlyMaskNonceStore T0) :
  core.ops.function.FnOnce (prover.prove_masked_with_attempt.closure_2 T0)
  (alloc.vec.Vec aspis_core.field.QM31) verifier.Error := {
  call_once :=
    prover.prove_masked_with_attempt.closure_2.Insts.CoreOpsFunctionFnOnceTupleVecQM31Error.call_once
    aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst
}

/-- [aspis_r1_cost_probe::prover::prove_masked_with_attempt::{impl core::ops::function::FnOnce<(aspis_statement::pool_v1::pair_tree_hiding::PoolV1PairHidingLayoutErrorV1,), aspis_r1_cost_probe::verifier::Error> for aspis_r1_cost_probe::prover::prove_masked_with_attempt::closure#1<T0>}::call_once]:
    Source: 'crates/aspis-r1-cost-probe/src/prover.rs', lines 196:69-196:87 -/
def
  prover.prove_masked_with_attempt.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairHidingLayoutErrorV1Error.call_once
  {T0 : Type} (aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst :
  aspis_prover.state_only_hiding.StateOnlyMaskNonceStore T0)
  (c : prover.prove_masked_with_attempt.closure_1 T0)
  (tupled_args :
  aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairHidingLayoutErrorV1) :
  Result verifier.Error
  := do
  ok verifier.Error.Semantic

/-- Trait implementation: [aspis_r1_cost_probe::prover::prove_masked_with_attempt::{impl core::ops::function::FnOnce<(aspis_statement::pool_v1::pair_tree_hiding::PoolV1PairHidingLayoutErrorV1,), aspis_r1_cost_probe::verifier::Error> for aspis_r1_cost_probe::prover::prove_masked_with_attempt::closure#1<T0>}]
    Source: 'crates/aspis-r1-cost-probe/src/prover.rs', lines 196:69-196:87 -/
@[reducible]
def
  prover.prove_masked_with_attempt.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairHidingLayoutErrorV1Error
  {T0 : Type} (aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst :
  aspis_prover.state_only_hiding.StateOnlyMaskNonceStore T0) :
  core.ops.function.FnOnce (prover.prove_masked_with_attempt.closure_1 T0)
  aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairHidingLayoutErrorV1
  verifier.Error := {
  call_once :=
    prover.prove_masked_with_attempt.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairHidingLayoutErrorV1Error.call_once
    aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst
}

/-- [aspis_r1_cost_probe::prover::prove_masked_with_attempt::{impl core::ops::function::FnOnce<(aspis_prover::state_only_hiding::StateOnlyMaskBuildError,), aspis_r1_cost_probe::verifier::Error> for aspis_r1_cost_probe::prover::prove_masked_with_attempt::closure<T0>}::call_once]:
    Source: 'crates/aspis-r1-cost-probe/src/prover.rs', lines 195:92-195:110 -/
def
  prover.prove_masked_with_attempt.closure.Insts.CoreOpsFunctionFnOnceTupleStateOnlyMaskBuildErrorError.call_once
  {T0 : Type} (aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst :
  aspis_prover.state_only_hiding.StateOnlyMaskNonceStore T0)
  (c : prover.prove_masked_with_attempt.closure T0)
  (tupled_args : aspis_prover.state_only_hiding.StateOnlyMaskBuildError) :
  Result verifier.Error
  := do
  ok verifier.Error.Semantic

/-- Trait implementation: [aspis_r1_cost_probe::prover::prove_masked_with_attempt::{impl core::ops::function::FnOnce<(aspis_prover::state_only_hiding::StateOnlyMaskBuildError,), aspis_r1_cost_probe::verifier::Error> for aspis_r1_cost_probe::prover::prove_masked_with_attempt::closure<T0>}]
    Source: 'crates/aspis-r1-cost-probe/src/prover.rs', lines 195:92-195:110 -/
@[reducible]
def
  prover.prove_masked_with_attempt.closure.Insts.CoreOpsFunctionFnOnceTupleStateOnlyMaskBuildErrorError
  {T0 : Type} (aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst :
  aspis_prover.state_only_hiding.StateOnlyMaskNonceStore T0) :
  core.ops.function.FnOnce (prover.prove_masked_with_attempt.closure T0)
  aspis_prover.state_only_hiding.StateOnlyMaskBuildError verifier.Error := {
  call_once :=
    prover.prove_masked_with_attempt.closure.Insts.CoreOpsFunctionFnOnceTupleStateOnlyMaskBuildErrorError.call_once
    aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst
}

/-- [aspis_r1_cost_probe::prover::prove_masked_with_attempt]:
    Source: 'crates/aspis-r1-cost-probe/src/prover.rs', lines 181:0-218:1 -/
def prover.prove_masked_with_attempt
  {T0 : Type} (aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst :
  aspis_prover.state_only_hiding.StateOnlyMaskNonceStore T0)
  (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (compiled :
  aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
  (variant : transport.Variant)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
  (binding : Array Std.U8 32#usize)
  (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets)
  (nonce_store : T0) :
  Result ((core.result.Result ((alloc.vec.Vec Std.U8) ×
    prover.MaskedFixtureAudit) verifier.Error) × T0)
  := do
  let (r, nonce_store1) ←
    aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.reserve_and_build_pool_v1_pair_forest_mask_material_v1
      aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst attempt hash
      binding context nonce_store
  let r1 ←
    core.result.Result.map_err (BuiltinFnOnce
      aspis_prover.state_only_hiding.StateOnlyMaskBuildError verifier.Error) r
      (prover.mask_error)
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let (reserved, material) := val
    let noised_c1 ←
      aspis_statement.state_only_trace.StateOnlyTraceFoundation.Insts.CoreCloneClone.clone
        compiled.semantic_c1
    let (r2, noised_c11) ←
      aspis_prover.state_only_hiding.apply_pool_v1_pair_forest_mask_material_v1
        noised_c1 material
    let r3 ←
      core.result.Result.map_err
        (prover.prove_masked_with_attempt.closure.Insts.CoreOpsFunctionFnOnceTupleStateOnlyMaskBuildErrorError
        aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst) r2 ()
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r3
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      let r4 ←
        aspis_statement.pool_v1.pair_forest_hiding.pool_v1_pair_forest_copy_active_row_masks_v1
      let r5 ←
        core.result.Result.map_err
          (prover.prove_masked_with_attempt.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairHidingLayoutErrorV1Error
          aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst) r4 ()
      let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r5
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val2 =>
        let r6 ←
          aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_pair_forest_zero_factor_d
            reserved hash context
        let r7 ←
          core.result.Result.map_err (BuiltinFnOnce
            aspis_prover.state_only_hiding.StateOnlyMaskBuildError
            verifier.Error) r6 (prover.mask_error)
        let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r7
        match cf3 with
        | core.ops.control_flow.ControlFlow.Continue val3 =>
          let r8 ←
            Array.Insts.CoreConvertTryFromVecVec.try_from Global 1024#usize
              val3
          let r9 ←
            core.result.Result.map_err
              (prover.prove_masked_with_attempt.closure_2.Insts.CoreOpsFunctionFnOnceTupleVecQM31Error
              aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst) r8 ()
          let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r9
          match cf4 with
          | core.ops.control_flow.ControlFlow.Continue val4 =>
            let i := alloc.vec.Vec.len val1.g
            if i != 1024#usize
            then
              ok (core.result.Result.Err verifier.Error.Semantic, nonce_store1)
            else
              let i1 := alloc.vec.Vec.len val1.h1_padding
              if i1 != 1024#usize
              then
                ok (core.result.Result.Err verifier.Error.Semantic,
                  nonce_store1)
              else
                let s := alloc.vec.Vec.deref val1.g
                let g ← prover.fixed_k_column s
                let s1 := alloc.vec.Vec.deref val1.h1_padding
                let h1_padding ← prover.fixed_k_column s1
                let s2 ← lift (Array.to_slice noised_c11.c1)
                let audit ←
                  prover.audit_masks s2 val1.mask_only_c1 val4 g h1_padding
                    val2
                if audit.c1_columns_inactive_balanced != 16#usize
                then
                  ok (core.result.Result.Err verifier.Error.Semantic,
                    nonce_store1)
                else
                  if audit.mask_only_columns_inactive_balanced != 10#usize
                  then
                    ok (core.result.Result.Err verifier.Error.Semantic,
                      nonce_store1)
                  else
                    if audit.d_inactive_balanced
                    then
                      if audit.g_inactive_balanced
                      then
                        if audit.h1_padding_inactive_balanced
                        then
                          let i2 ← aspis_core.r0.merkle.C1_TAG
                          let r10 ←
                            prover.derive_private_salts reserved context hash
                              i2
                          let cf5 ←
                            core.result.Result.Insts.CoreOpsTry.branch r10
                          match cf5 with
                          | core.ops.control_flow.ControlFlow.Continue val5 =>
                            let i3 ← aspis_core.r0.merkle.C2_TAG
                            let r11 ←
                              prover.derive_private_salts reserved context hash
                                i3
                            let cf6 ←
                              core.result.Result.Insts.CoreOpsTry.branch r11
                            match cf6 with
                            | core.ops.control_flow.ControlFlow.Continue val6
                              =>
                              let r12 ← host_commitment.EncodingDomain.new
                              let r13 ←
                                core.result.Result.map_err
                                  (prover.prove_masked_with_attempt.closure_3.Insts.CoreOpsFunctionFnOnceTupleErrorError
                                  aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst)
                                  r12 ()
                              let cf7 ←
                                core.result.Result.Insts.CoreOpsTry.branch r13
                              match cf7 with
                              | core.ops.control_flow.ControlFlow.Continue val7
                                =>
                                let we ←
                                  aspis_core.field.wide_exact.WideExact.ZERO
                                let a := Array.repeat 1024#usize we
                                let v ←
                                  alloc.vec.from_elem (core.clone.CloneArray
                                    1024#usize
                                    aspis_core.field.wide_exact.WideExact.Insts.CoreCloneClone)
                                    a 29#usize
                                let (r14, backend) ←
                                  host_semantic.build_with_material
                                    aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32
                                    prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments
                                    public1 compiled noised_c11
                                    val1.mask_only_c1 val4 g h1_padding
                                    {
                                      hash,
                                      variant,
                                      domain := val7,
                                      messages := v,
                                      c1 := none,
                                      c2 := none,
                                      c1_salts := (some val5),
                                      c2_salts := (some val6)
                                    } hash variant
                                let r15 ←
                                  core.result.Result.map_err (BuiltinFnOnce
                                    r1_wire.Error verifier.Error) r14
                                    (prover.semantic_error)
                                let cf8 ←
                                  core.result.Result.Insts.CoreOpsTry.branch
                                    r15
                                match cf8 with
                                | core.ops.control_flow.ControlFlow.Continue
                                  val8 =>
                                  let v1 ←
                                    Array.index_usize val8.columns 26#usize
                                  let s3 := alloc.vec.Vec.deref v1
                                  let o ←
                                    aspis_statement.state_only_semantic.state_only_copy_helper_sum
                                      s3
                                  let q ← aspis_core.field.QM31.ZERO
                                  let h1_total_balanced ←
                                    core.option.Option.Insts.CoreCmpPartialEqOption.eq
                                      aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
                                      o (some q)
                                  if h1_total_balanced
                                  then
                                    let r16 ←
                                      prover.prove_from_semantics public1
                                        variant hash backend val8 (reserved,
                                        context)
                                    let cf9 ←
                                      core.result.Result.Insts.CoreOpsTry.branch
                                        r16
                                    match cf9 with
                                    |
                                      core.ops.control_flow.ControlFlow.Continue
                                      val9 =>
                                      ok (core.result.Result.Ok (val9,
                                        { audit with h1_total_balanced := true
                                        }), nonce_store1)
                                    | core.ops.control_flow.ControlFlow.Break
                                      residual =>
                                      let r17 ←
                                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                          ((alloc.vec.Vec Std.U8) ×
                                          prover.MaskedFixtureAudit)
                                          (core.convert.FromSame
                                          verifier.Error) residual
                                      ok (r17, nonce_store1)
                                  else
                                    ok (core.result.Result.Err
                                      verifier.Error.Semantic, nonce_store1)
                                | core.ops.control_flow.ControlFlow.Break
                                  residual =>
                                  let r16 ←
                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                      ((alloc.vec.Vec Std.U8) ×
                                      prover.MaskedFixtureAudit)
                                      (core.convert.FromSame verifier.Error)
                                      residual
                                  ok (r16, nonce_store1)
                              | core.ops.control_flow.ControlFlow.Break
                                residual =>
                                let r14 ←
                                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                    ((alloc.vec.Vec Std.U8) ×
                                    prover.MaskedFixtureAudit)
                                    (core.convert.FromSame verifier.Error)
                                    residual
                                ok (r14, nonce_store1)
                            | core.ops.control_flow.ControlFlow.Break residual
                              =>
                              let r12 ←
                                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                  ((alloc.vec.Vec Std.U8) ×
                                  prover.MaskedFixtureAudit)
                                  (core.convert.FromSame verifier.Error)
                                  residual
                              ok (r12, nonce_store1)
                          | core.ops.control_flow.ControlFlow.Break residual =>
                            let r11 ←
                              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                ((alloc.vec.Vec Std.U8) ×
                                prover.MaskedFixtureAudit)
                                (core.convert.FromSame verifier.Error) residual
                            ok (r11, nonce_store1)
                        else
                          ok (core.result.Result.Err verifier.Error.Semantic,
                            nonce_store1)
                      else
                        ok (core.result.Result.Err verifier.Error.Semantic,
                          nonce_store1)
                    else
                      ok (core.result.Result.Err verifier.Error.Semantic,
                        nonce_store1)
          | core.ops.control_flow.ControlFlow.Break residual =>
            let r10 ←
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                ((alloc.vec.Vec Std.U8) × prover.MaskedFixtureAudit)
                (core.convert.FromSame verifier.Error) residual
            ok (r10, nonce_store1)
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r8 ←
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              ((alloc.vec.Vec Std.U8) × prover.MaskedFixtureAudit)
              (core.convert.FromSame verifier.Error) residual
          ok (r8, nonce_store1)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r6 ←
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            ((alloc.vec.Vec Std.U8) × prover.MaskedFixtureAudit)
            (core.convert.FromSame verifier.Error) residual
        ok (r6, nonce_store1)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r4 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          ((alloc.vec.Vec Std.U8) × prover.MaskedFixtureAudit)
          (core.convert.FromSame verifier.Error) residual
      ok (r4, nonce_store1)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r2 ←
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        ((alloc.vec.Vec Std.U8) × prover.MaskedFixtureAudit)
        (core.convert.FromSame verifier.Error) residual
    ok (r2, nonce_store1)

/-- [aspis_r1_cost_probe::prover::prove_masked_attempt::{impl core::ops::function::FnOnce<(aspis_core::state_only_prefix::r0::Error,), aspis_r1_cost_probe::verifier::Error> for aspis_r1_cost_probe::prover::prove_masked_attempt::closure}::call_once]:
    Source: 'crates/aspis-r1-cost-probe/src/prover.rs', lines 175:51-175:69 -/
def
  prover.prove_masked_attempt.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once
  (c : prover.prove_masked_attempt.closure)
  (tupled_args : aspis_core.state_only_prefix.r0.Error) :
  Result verifier.Error
  := do
  ok verifier.Error.Semantic

/-- Trait implementation: [aspis_r1_cost_probe::prover::prove_masked_attempt::{impl core::ops::function::FnOnce<(aspis_core::state_only_prefix::r0::Error,), aspis_r1_cost_probe::verifier::Error> for aspis_r1_cost_probe::prover::prove_masked_attempt::closure}]
    Source: 'crates/aspis-r1-cost-probe/src/prover.rs', lines 175:51-175:69 -/
@[reducible]
def
  prover.prove_masked_attempt.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError
  : core.ops.function.FnOnce prover.prove_masked_attempt.closure
  aspis_core.state_only_prefix.r0.Error verifier.Error := {
  call_once :=
    prover.prove_masked_attempt.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once
}

/-- [aspis_r1_cost_probe::prover::prove_masked_attempt]:
    Source: 'crates/aspis-r1-cost-probe/src/prover.rs', lines 167:0-179:1
    Visibility: public -/
def prover.prove_masked_attempt
  (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (compiled :
  aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
  (variant : transport.Variant)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets)
  (nonce_store :
  aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore) :
  Result ((core.result.Result ((alloc.vec.Vec Std.U8) ×
    prover.MaskedFixtureAudit) verifier.Error) ×
    aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore)
  := do
  let r ←
    aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
      public1
  let r1 ←
    core.result.Result.map_err
      prover.prove_masked_attempt.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError
      r ()
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let s := alloc.vec.Vec.deref val
    let s1 ← lift (Array.to_slice (Array.make 1#usize [ s ]))
    let a ← hash s1
    let a1 ←
      aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.impl.mask_nonce
        attempt
    let context ←
      aspis_core.state_only_hiding.StateOnlyHidingContext.pool_v1_pair_forest_v1
        a a1
    let s2 ←
      lift (Array.to_slice
        (Array.make 30#usize [
          85#u8, 78#u8, 80#u8, 82#u8, 79#u8, 86#u8, 69#u8, 68#u8, 58#u8, 82#u8,
          49#u8, 58#u8, 80#u8, 51#u8, 58#u8, 80#u8, 82#u8, 73#u8, 86#u8, 65#u8,
          84#u8, 69#u8, 45#u8, 65#u8, 84#u8, 84#u8, 69#u8, 77#u8, 80#u8, 84#u8
          ]))
    let s3 := alloc.vec.Vec.deref val
    let i ← transport.Variant.tag variant
    let s4 ← lift (Array.to_slice (Array.make 1#usize [ i ]))
    let a2 ←
      aspis_core.state_only_hiding.StateOnlyHidingContext.encode context
    let s5 ← lift (Array.to_slice a2)
    let s6 ← lift (Array.to_slice (Array.make 4#usize [ s2, s3, s4, s5 ]))
    let binding ← hash s6
    prover.prove_masked_with_attempt
      aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore
      public1 compiled variant hash context binding attempt nonce_store
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r2 ←
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        ((alloc.vec.Vec Std.U8) × prover.MaskedFixtureAudit)
        (core.convert.FromSame verifier.Error) residual
    ok (r2, nonce_store)

end ProverRwRngNativeBody
