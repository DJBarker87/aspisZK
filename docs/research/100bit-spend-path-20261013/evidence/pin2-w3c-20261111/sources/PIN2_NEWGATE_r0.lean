-- PIN2 NEW GATE for the r0 module (public_bytes root) at source 271869c946d4286db6ee5be784f136599fa8707e (W1 fix/pin2-verifier-20261110).
-- Emission PCXQ_E001: Charon 454586e9 + Aeneas 0d21a9ec (second tool version), overflow-checks ON, features r0,pool-v1-kernel,+audit set, cargo --jobs 4 / CARGO_BUILD_JOBS=4, rustc -Zthreads=1,
-- --include aspis_core::field::P, identity by class receipt PCWE_E003. Raw emission sha256: Types.lean ad5c82bdd9b43f2dc1ea78ebb9e354dceb0bca7b71c1c16f530423cca1c17bec Funs.lean 5faa94e0fa15d161b3bd23ffc51d6ac91d61f81dfb5eea99209d47e822b69174
-- Built by PCXQ_mk_newgate_r0.py (transformations listed there). Contains no placeholder proof and no axiom.
import Aeneas
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option maxRecDepth 2048

namespace PCWN_NewLib
open Aeneas.Std
/-- The Never type in Rust -/
inductive Never where

def core.result.Result.Insts.CoreOpsTry.branch
  {T E : Type _} :
  core.result.Result T E →
    Std.Result (core.ops.control_flow.ControlFlow
      (core.result.Result Never E) T)
  | .Ok v => .ok (.Continue v)
  | .Err e => .ok (.Break (.Err e))

def core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
  (T : Type _) {E F : Type _} (convertFromInst : core.convert.From F E)
  (r : core.result.Result Never E) : Std.Result (core.result.Result T F) :=
  match r with
  | .Ok x => x.casesOn
  | .Err e => do
      let v ← convertFromInst.from e
      .ok (.Err v)

/-- transport of the empty type: gate Infallible -> new Never -/
def castN (x : core.convert.Infallible) : PCWN_NewLib.Never := x.casesOn
def castR {E : Type} : core.result.Result core.convert.Infallible E → core.result.Result PCWN_NewLib.Never E
  | .Ok x => .Ok (castN x)
  | .Err e => .Err e

set_option maxHeartbeats 200000 in
/-- ITEM: new-library from_residual = gate-library from_residual, transported along the empty-type map. -/
theorem from_residual_eq (T : Type) {E F : Type} (inst : core.convert.From F E)
    (r : core.result.Result core.convert.Infallible E) :
    PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual T inst (castR r)
      = Aeneas.Std.core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual T inst r := by
  cases r with
  | Ok x => exact x.casesOn
  | Err e => rfl
#print axioms from_residual_eq

set_option maxHeartbeats 200000 in
/-- branch bind-transport: Continue arms agree, Break arms agree on the transported residual (used by pb_chain). -/
theorem branch_bind {T E A : Type} (r : core.result.Result T E)
    (F : core.ops.control_flow.ControlFlow (core.result.Result PCWN_NewLib.Never E) T → Result A)
    (G : core.ops.control_flow.ControlFlow (core.result.Result core.convert.Infallible E) T → Result A)
    (hOk : ∀ v, F (.Continue v) = G (.Continue v)) (hErr : ∀ e, F (.Break (.Err e)) = G (.Break (.Err e))) :
    Bind.bind (PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r) F
      = Bind.bind (Aeneas.Std.core.result.Result.Insts.CoreOpsTry.branch r) G := by
  cases r with
  | Ok v => exact hOk v
  | Err e => exact hErr e
#print axioms branch_bind
end PCWN_NewLib

/- Aeneas-generated default heartbeat budget for the emitted definitions (no theorem below this line except the audit prints). -/
set_option maxHeartbeats 1000000

namespace AspisR1PublicPreparationPIN2


/-- [aspis_core::field::M31]
    Source: 'crates/aspis-core/src/field.rs', lines 23:0-23:14
    Name pattern: [aspis_core::field::M31]
    Visibility: public -/
@[reducible]
def aspis_core.field.M31 := Std.U32

/-- [aspis_core::state_only_prefix::r0::Error]
    Source: 'crates/aspis-core/src/state_only_prefix.rs', lines 1629:4-1629:18
    Name pattern: [aspis_core::state_only_prefix::r0::Error]
    Visibility: public -/
inductive aspis_core.state_only_prefix.r0.Error where
| Allocation : aspis_core.state_only_prefix.r0.Error
| RowOrder : Std.U8 → Std.U8 → aspis_core.state_only_prefix.r0.Error
| InvalidRow : aspis_core.state_only_prefix.r0.Error
| Tag : Std.U8 → aspis_core.state_only_prefix.r0.Error
| Length : Std.U8 → aspis_core.state_only_prefix.r0.Error
| NonCanonical : Std.U8 → Std.Usize → aspis_core.state_only_prefix.r0.Error
| Boundary : Std.Usize → aspis_core.state_only_prefix.r0.Error
| Terminal : aspis_core.state_only_prefix.r0.Error
| EqualCirclePoints : aspis_core.state_only_prefix.r0.Error
| TrailingBytes : aspis_core.state_only_prefix.r0.Error
| Public : aspis_core.state_only_prefix.r0.Error

/- PIN2 W3c (overlay copy): `@[discriminant isize]` replaced by the definition the
   attribute generates plus an explicitly named instance inside this namespace, so the
   instance no longer lands at top level as `instDiscriminant<Ty>Isize` (clash with the
   gate module AspisR1FinishRelationCurrent.Types). Discriminant values: 0..n-1 in
   constructor order, as the attribute assigns. -/
def aspis_core.state_only_prefix.r0.Error.read_discriminant (x : aspis_core.state_only_prefix.r0.Error) : Std.Isize :=
  match x with
  | .Allocation => 0#isize
  | .RowOrder _ _ => 1#isize
  | .InvalidRow => 2#isize
  | .Tag _ => 3#isize
  | .Length _ => 4#isize
  | .NonCanonical _ _ => 5#isize
  | .Boundary _ => 6#isize
  | .Terminal => 7#isize
  | .EqualCirclePoints => 8#isize
  | .TrailingBytes => 9#isize
  | .Public => 10#isize

instance instDiscriminant_PIN2_r0_StateOnlyPrefixError_Isize : Aeneas.Std.Discriminant aspis_core.state_only_prefix.r0.Error Std.Isize where
  read_discriminant := aspis_core.state_only_prefix.r0.Error.read_discriminant

/-- [aspis_statement::pool_v1::pair_forest_semantic_terminal::CompiledVariant]
    Source: 'crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs', lines 81:0-84:1 -/
inductive pool_v1.pair_forest_semantic_terminal.CompiledVariant where
| PrivateTransfer : pool_v1.pair_forest_semantic_terminal.CompiledVariant
| Withdrawal : pool_v1.pair_forest_semantic_terminal.CompiledVariant

/- PIN2 W3c (overlay copy): `@[discriminant isize]` replaced by the definition the
   attribute generates plus an explicitly named instance inside this namespace, so the
   instance no longer lands at top level as `instDiscriminant<Ty>Isize` (clash with the
   gate module AspisR1FinishRelationCurrent.Types). Discriminant values: 0..n-1 in
   constructor order, as the attribute assigns. -/
def pool_v1.pair_forest_semantic_terminal.CompiledVariant.read_discriminant (x : pool_v1.pair_forest_semantic_terminal.CompiledVariant) : Std.Isize :=
  match x with
  | .PrivateTransfer => 0#isize
  | .Withdrawal => 1#isize

instance instDiscriminant_PIN2_r0_CompiledVariant_Isize : Aeneas.Std.Discriminant pool_v1.pair_forest_semantic_terminal.CompiledVariant Std.Isize where
  read_discriminant := pool_v1.pair_forest_semantic_terminal.CompiledVariant.read_discriminant

/-- [aspis_statement::pool_v1::pair_tree_profile::PoolV1PairLiveSnapshotV1]
    Source: 'crates/aspis-statement/src/pool_v1/pair_tree_profile.rs', lines 404:0-411:1
    Visibility: public -/
structure pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 where
  pool : Array Std.U8 32#usize
  deployment_domain : Array Std.U8 32#usize
  sequence : Std.U64
  next_pair_index : Std.U64
  current_root : Array aspis_core.field.M31 8#usize
  frontier : Array (Array aspis_core.field.M31 8#usize) 20#usize

/-- [aspis_statement::pool_v1::pair_terminal::PoolV1PairVerifiedAfterstateV1]
    Source: 'crates/aspis-statement/src/pool_v1/pair_terminal.rs', lines 116:0-120:1
    Visibility: public -/
structure pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 where
  next_pair_index : Std.U64
  next_root : Array aspis_core.field.M31 8#usize
  next_frontier : Array (Array aspis_core.field.M31 8#usize) 20#usize

/-- [aspis_statement::pool_v1::pair_tree_profile::PoolV1PairLatePublicStatementV1]
    Source: 'crates/aspis-statement/src/pool_v1/pair_tree_profile.rs', lines 414:0-419:1
    Visibility: public -/
structure pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 where
  live_snapshot : pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1
  candidate_afterstate : pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1

/-- [aspis_statement::pool_v1::pair_forest_semantic_terminal::SemanticPublic]
    Source: 'crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs', lines 87:0-101:1 -/
structure pool_v1.pair_forest_semantic_terminal.SemanticPublic where
  variant : pool_v1.pair_forest_semantic_terminal.CompiledVariant
  pool : Array Std.U8 32#usize
  deployment_domain : Array Std.U8 32#usize
  anchor : Array aspis_core.field.M31 8#usize
  nullifier : Array aspis_core.field.M31 8#usize
  asset_id : aspis_core.field.M31
  recipient : Option (Array aspis_core.field.M31 8#usize)
  change : Array aspis_core.field.M31 8#usize
  withdrawal_amount : Option Std.U32
  destination : Option (Array Std.U8 32#usize)
  transition : pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1

/-- [aspis_statement::pool_v1::payment_relation::PoolV1PrivateTransferPublicV1]
    Source: 'crates/aspis-statement/src/pool_v1/payment_relation.rs', lines 46:0-55:1
    Visibility: public -/
structure pool_v1.payment_relation.PoolV1PrivateTransferPublicV1 where
  pool : Array Std.U8 32#usize
  deployment_domain : Array Std.U8 32#usize
  anchor_sequence : Std.U64
  anchor_root : Array aspis_core.field.M31 8#usize
  nullifier : Array aspis_core.field.M31 8#usize
  asset_id : aspis_core.field.M31
  recipient_commitment : Array aspis_core.field.M31 8#usize
  change_commitment : Array aspis_core.field.M31 8#usize

/-- [aspis_statement::pool_v1::payment_relation::PoolV1WithdrawalPublicV1]
    Source: 'crates/aspis-statement/src/pool_v1/payment_relation.rs', lines 58:0-68:1
    Visibility: public -/
structure pool_v1.payment_relation.PoolV1WithdrawalPublicV1 where
  pool : Array Std.U8 32#usize
  deployment_domain : Array Std.U8 32#usize
  anchor_sequence : Std.U64
  anchor_root : Array aspis_core.field.M31 8#usize
  nullifier : Array aspis_core.field.M31 8#usize
  asset_id : aspis_core.field.M31
  amount : Std.U32
  destination_token_account : Array Std.U8 32#usize
  change_commitment : Array aspis_core.field.M31 8#usize

/-- [aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::Public]
    Source: 'crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs', lines 1999:4-2008:5
    Visibility: public -/
inductive pool_v1.pair_forest_semantic_terminal.r0.Public where
| Transfer :
  pool_v1.payment_relation.PoolV1PrivateTransferPublicV1 →
  pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 →
  pool_v1.pair_forest_semantic_terminal.r0.Public
| Withdrawal :
  pool_v1.payment_relation.PoolV1WithdrawalPublicV1 →
  pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 →
  pool_v1.pair_forest_semantic_terminal.r0.Public

/- PIN2 W3c (overlay copy): `@[discriminant isize]` replaced by the definition the
   attribute generates plus an explicitly named instance inside this namespace, so the
   instance no longer lands at top level as `instDiscriminant<Ty>Isize` (clash with the
   gate module AspisR1FinishRelationCurrent.Types). Discriminant values: 0..n-1 in
   constructor order, as the attribute assigns. -/
def pool_v1.pair_forest_semantic_terminal.r0.Public.read_discriminant (x : pool_v1.pair_forest_semantic_terminal.r0.Public) : Std.Isize :=
  match x with
  | .Transfer _ _ => 0#isize
  | .Withdrawal _ _ => 1#isize

instance instDiscriminant_PIN2_r0_Public_Isize : Aeneas.Std.Discriminant pool_v1.pair_forest_semantic_terminal.r0.Public Std.Isize where
  read_discriminant := pool_v1.pair_forest_semantic_terminal.r0.Public.read_discriminant




/-- [aspis_core::field::P]
    Source: 'crates/aspis-core/src/field.rs', lines 19:0-19:16
    Name pattern: [aspis_core::field::P]
    Visibility: public -/
@[global_simps, irreducible]
def aspis_core.field.P : Std.U32 := 2147483647#u32

/-- [aspis_statement::pool_v1::pair_forest_semantic_terminal::private_public]:
    Source: 'crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs', lines 1330:0-1347:1 -/
def pool_v1.pair_forest_semantic_terminal.private_public
  («public» : pool_v1.payment_relation.PoolV1PrivateTransferPublicV1)
  (transition : pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) :
  Result pool_v1.pair_forest_semantic_terminal.SemanticPublic
  := do
  ok
    {
      variant :=
        pool_v1.pair_forest_semantic_terminal.CompiledVariant.PrivateTransfer,
      pool := «public».pool,
      deployment_domain := «public».deployment_domain,
      anchor := «public».anchor_root,
      nullifier := «public».nullifier,
      asset_id := «public».asset_id,
      recipient := (some «public».recipient_commitment),
      change := «public».change_commitment,
      withdrawal_amount := none,
      destination := none,
      transition
    }

/-- [aspis_statement::pool_v1::pair_forest_semantic_terminal::withdrawal_public]:
    Source: 'crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs', lines 1349:0-1366:1 -/
def pool_v1.pair_forest_semantic_terminal.withdrawal_public
  («public» : pool_v1.payment_relation.PoolV1WithdrawalPublicV1)
  (transition : pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) :
  Result pool_v1.pair_forest_semantic_terminal.SemanticPublic
  := do
  ok
    {
      variant :=
        pool_v1.pair_forest_semantic_terminal.CompiledVariant.Withdrawal,
      pool := «public».pool,
      deployment_domain := «public».deployment_domain,
      anchor := «public».anchor_root,
      nullifier := «public».nullifier,
      asset_id := «public».asset_id,
      recipient := none,
      change := «public».change_commitment,
      withdrawal_amount := (some «public».amount),
      destination := (some «public».destination_token_account),
      transition
    }

/-- [aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::{aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::Public<'a>}::semantic]:
    Source: 'crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs', lines 2010:8-2015:9 -/
def pool_v1.pair_forest_semantic_terminal.r0.Public.semantic
  (self : pool_v1.pair_forest_semantic_terminal.r0.Public) :
  Result pool_v1.pair_forest_semantic_terminal.SemanticPublic
  := do
  match self with
  | pool_v1.pair_forest_semantic_terminal.r0.Public.Transfer «public»
    transition =>
    pool_v1.pair_forest_semantic_terminal.private_public «public» transition
  | pool_v1.pair_forest_semantic_terminal.r0.Public.Withdrawal «public»
    transition =>
    pool_v1.pair_forest_semantic_terminal.withdrawal_public «public»
      transition

/-- [aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::{aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::Public<'a>}::public_bytes::fields]: loop body 0:
    Source: 'crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs', lines 2028:16-2035:13 -/
def
  pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields_loop.body
  (iter : core.slice.iter.Iter aspis_core.field.M31)
  (out : alloc.vec.Vec Std.U8) :
  Result (ControlFlow ((core.slice.iter.Iter aspis_core.field.M31) ×
    (alloc.vec.Vec Std.U8)) ((core.result.Result Unit
    aspis_core.state_only_prefix.r0.Error) × (alloc.vec.Vec Std.U8)))
  := do
  let (o, iter1) ← core.slice.iter.IteratorSliceIter.next iter
  match o with
  | none => ok (done (core.result.Result.Ok (), out))
  | some value =>
    if value >= aspis_core.field.P
    then
      ok (done (core.result.Result.Err
        aspis_core.state_only_prefix.r0.Error.Public, out))
    else
      let a ← lift (core.num.U32.to_le_bytes value)
      let s ← lift (Array.to_slice a)
      let out1 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out s
      ok (cont (iter1, out1))

/-- [aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::{aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::Public<'a>}::public_bytes::fields]: loop 0:
    Source: 'crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs', lines 2028:16-2035:13 -/
def pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields_loop
  (iter : core.slice.iter.Iter aspis_core.field.M31)
  (out : alloc.vec.Vec Std.U8) :
  Result ((core.result.Result Unit aspis_core.state_only_prefix.r0.Error) ×
    (alloc.vec.Vec Std.U8))
  := do
  loop
    (fun (iter1, out1) =>
      pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields_loop.body
      iter1 out1)
    (iter, out)

/-- [aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::{aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::Public<'a>}::public_bytes::fields]:
    Source: 'crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs', lines 2027:12-2035:13 -/
def pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields
  (out : alloc.vec.Vec Std.U8) (values : Slice aspis_core.field.M31) :
  Result ((core.result.Result Unit aspis_core.state_only_prefix.r0.Error) ×
    (alloc.vec.Vec Std.U8))
  := do
  let iter ←
    SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter
      values
  pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields_loop iter
    out

/-- [aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::{aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::Public<'a>}::public_bytes::frontier]:
    Source: 'crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs', lines 2038:12-2060:13 -/
def pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.frontier
  (out : alloc.vec.Vec Std.U8)
  (values : Array (Array aspis_core.field.M31 8#usize) 20#usize) :
  Result ((core.result.Result Unit aspis_core.state_only_prefix.r0.Error) ×
    (alloc.vec.Vec Std.U8))
  := do
  let a ← Array.index_usize values 0#usize
  let s ← lift (Array.to_slice a)
  let (r, out1) ←
    pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields out s
  let cf ← PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    let a1 ← Array.index_usize values 1#usize
    let s1 ← lift (Array.to_slice a1)
    let (r1, out2) ←
      pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields out1
        s1
    let cf1 ← PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let a2 ← Array.index_usize values 2#usize
      let s2 ← lift (Array.to_slice a2)
      let (r2, out3) ←
        pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields
          out2 s2
      let cf2 ← PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r2
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        let a3 ← Array.index_usize values 3#usize
        let s3 ← lift (Array.to_slice a3)
        let (r3, out4) ←
          pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields
            out3 s3
        let cf3 ← PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r3
        match cf3 with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          let a4 ← Array.index_usize values 4#usize
          let s4 ← lift (Array.to_slice a4)
          let (r4, out5) ←
            pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields
              out4 s4
          let cf4 ← PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r4
          match cf4 with
          | core.ops.control_flow.ControlFlow.Continue _ =>
            let a5 ← Array.index_usize values 5#usize
            let s5 ← lift (Array.to_slice a5)
            let (r5, out6) ←
              pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields
                out5 s5
            let cf5 ← PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r5
            match cf5 with
            | core.ops.control_flow.ControlFlow.Continue _ =>
              let a6 ← Array.index_usize values 6#usize
              let s6 ← lift (Array.to_slice a6)
              let (r6, out7) ←
                pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields
                  out6 s6
              let cf6 ← PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r6
              match cf6 with
              | core.ops.control_flow.ControlFlow.Continue _ =>
                let a7 ← Array.index_usize values 7#usize
                let s7 ← lift (Array.to_slice a7)
                let (r7, out8) ←
                  pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields
                    out7 s7
                let cf7 ← PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r7
                match cf7 with
                | core.ops.control_flow.ControlFlow.Continue _ =>
                  let a8 ← Array.index_usize values 8#usize
                  let s8 ← lift (Array.to_slice a8)
                  let (r8, out9) ←
                    pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields
                      out8 s8
                  let cf8 ← PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r8
                  match cf8 with
                  | core.ops.control_flow.ControlFlow.Continue _ =>
                    let a9 ← Array.index_usize values 9#usize
                    let s9 ← lift (Array.to_slice a9)
                    let (r9, out10) ←
                      pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields
                        out9 s9
                    let cf9 ← PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r9
                    match cf9 with
                    | core.ops.control_flow.ControlFlow.Continue _ =>
                      let a10 ← Array.index_usize values 10#usize
                      let s10 ← lift (Array.to_slice a10)
                      let (r10, out11) ←
                        pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields
                          out10 s10
                      let cf10 ←
                        PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r10
                      match cf10 with
                      | core.ops.control_flow.ControlFlow.Continue _ =>
                        let a11 ← Array.index_usize values 11#usize
                        let s11 ← lift (Array.to_slice a11)
                        let (r11, out12) ←
                          pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields
                            out11 s11
                        let cf11 ←
                          PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r11
                        match cf11 with
                        | core.ops.control_flow.ControlFlow.Continue _ =>
                          let a12 ← Array.index_usize values 12#usize
                          let s12 ← lift (Array.to_slice a12)
                          let (r12, out13) ←
                            pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields
                              out12 s12
                          let cf12 ←
                            PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r12
                          match cf12 with
                          | core.ops.control_flow.ControlFlow.Continue _ =>
                            let a13 ← Array.index_usize values 13#usize
                            let s13 ← lift (Array.to_slice a13)
                            let (r13, out14) ←
                              pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields
                                out13 s13
                            let cf13 ←
                              PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r13
                            match cf13 with
                            | core.ops.control_flow.ControlFlow.Continue _ =>
                              let a14 ← Array.index_usize values 14#usize
                              let s14 ← lift (Array.to_slice a14)
                              let (r14, out15) ←
                                pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields
                                  out14 s14
                              let cf14 ←
                                PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r14
                              match cf14 with
                              | core.ops.control_flow.ControlFlow.Continue _ =>
                                let a15 ← Array.index_usize values 15#usize
                                let s15 ← lift (Array.to_slice a15)
                                let (r15, out16) ←
                                  pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields
                                    out15 s15
                                let cf15 ←
                                  PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch
                                    r15
                                match cf15 with
                                | core.ops.control_flow.ControlFlow.Continue _
                                  =>
                                  let a16 ← Array.index_usize values 16#usize
                                  let s16 ← lift (Array.to_slice a16)
                                  let (r16, out17) ←
                                    pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields
                                      out16 s16
                                  let cf16 ←
                                    PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch
                                      r16
                                  match cf16 with
                                  | core.ops.control_flow.ControlFlow.Continue
                                    _ =>
                                    let a17 ←
                                      Array.index_usize values 17#usize
                                    let s17 ← lift (Array.to_slice a17)
                                    let (r17, out18) ←
                                      pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields
                                        out17 s17
                                    let cf17 ←
                                      PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch
                                        r17
                                    match cf17 with
                                    |
                                      core.ops.control_flow.ControlFlow.Continue
                                      _ =>
                                      let a18 ←
                                        Array.index_usize values 18#usize
                                      let s18 ← lift (Array.to_slice a18)
                                      let (r18, out19) ←
                                        pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields
                                          out18 s18
                                      let cf18 ←
                                        PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch
                                          r18
                                      match cf18 with
                                      |
                                        core.ops.control_flow.ControlFlow.Continue
                                        _ =>
                                        let a19 ←
                                          Array.index_usize values 19#usize
                                        let s19 ← lift (Array.to_slice a19)
                                        let (r19, out20) ←
                                          pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields
                                            out19 s19
                                        let cf19 ←
                                          PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch
                                            r19
                                        match cf19 with
                                        |
                                          core.ops.control_flow.ControlFlow.Continue
                                          _ =>
                                          ok (core.result.Result.Ok (), out20)
                                        |
                                          core.ops.control_flow.ControlFlow.Break
                                          residual =>
                                          let r20 ←
                                            PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                              Unit (core.convert.FromSame
                                              aspis_core.state_only_prefix.r0.Error)
                                              residual
                                          ok (r20, out20)
                                      | core.ops.control_flow.ControlFlow.Break
                                        residual =>
                                        let r19 ←
                                          PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                            Unit (core.convert.FromSame
                                            aspis_core.state_only_prefix.r0.Error)
                                            residual
                                        ok (r19, out19)
                                    | core.ops.control_flow.ControlFlow.Break
                                      residual =>
                                      let r18 ←
                                        PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                          Unit (core.convert.FromSame
                                          aspis_core.state_only_prefix.r0.Error)
                                          residual
                                      ok (r18, out18)
                                  | core.ops.control_flow.ControlFlow.Break
                                    residual =>
                                    let r17 ←
                                      PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                        Unit (core.convert.FromSame
                                        aspis_core.state_only_prefix.r0.Error)
                                        residual
                                    ok (r17, out17)
                                | core.ops.control_flow.ControlFlow.Break
                                  residual =>
                                  let r16 ←
                                    PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                      Unit (core.convert.FromSame
                                      aspis_core.state_only_prefix.r0.Error)
                                      residual
                                  ok (r16, out16)
                              | core.ops.control_flow.ControlFlow.Break
                                residual =>
                                let r15 ←
                                  PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                    Unit (core.convert.FromSame
                                    aspis_core.state_only_prefix.r0.Error)
                                    residual
                                ok (r15, out15)
                            | core.ops.control_flow.ControlFlow.Break residual
                              =>
                              let r14 ←
                                PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                  Unit (core.convert.FromSame
                                  aspis_core.state_only_prefix.r0.Error)
                                  residual
                              ok (r14, out14)
                          | core.ops.control_flow.ControlFlow.Break residual =>
                            let r13 ←
                              PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                Unit (core.convert.FromSame
                                aspis_core.state_only_prefix.r0.Error) residual
                            ok (r13, out13)
                        | core.ops.control_flow.ControlFlow.Break residual =>
                          let r12 ←
                            PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                              Unit (core.convert.FromSame
                              aspis_core.state_only_prefix.r0.Error) residual
                          ok (r12, out12)
                      | core.ops.control_flow.ControlFlow.Break residual =>
                        let r11 ←
                          PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                            Unit (core.convert.FromSame
                            aspis_core.state_only_prefix.r0.Error) residual
                        ok (r11, out11)
                    | core.ops.control_flow.ControlFlow.Break residual =>
                      let r10 ←
                        PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                          Unit (core.convert.FromSame
                          aspis_core.state_only_prefix.r0.Error) residual
                      ok (r10, out10)
                  | core.ops.control_flow.ControlFlow.Break residual =>
                    let r9 ←
                      PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                        Unit (core.convert.FromSame
                        aspis_core.state_only_prefix.r0.Error) residual
                    ok (r9, out9)
                | core.ops.control_flow.ControlFlow.Break residual =>
                  let r8 ←
                    PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                      Unit (core.convert.FromSame
                      aspis_core.state_only_prefix.r0.Error) residual
                  ok (r8, out8)
              | core.ops.control_flow.ControlFlow.Break residual =>
                let r7 ←
                  PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                    Unit (core.convert.FromSame
                    aspis_core.state_only_prefix.r0.Error) residual
                ok (r7, out7)
            | core.ops.control_flow.ControlFlow.Break residual =>
              let r6 ←
                PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                  Unit (core.convert.FromSame
                  aspis_core.state_only_prefix.r0.Error) residual
              ok (r6, out6)
          | core.ops.control_flow.ControlFlow.Break residual =>
            let r5 ←
              PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                Unit (core.convert.FromSame
                aspis_core.state_only_prefix.r0.Error) residual
            ok (r5, out5)
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r4 ←
            PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              Unit (core.convert.FromSame
              aspis_core.state_only_prefix.r0.Error) residual
          ok (r4, out4)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r3 ←
          PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            Unit (core.convert.FromSame aspis_core.state_only_prefix.r0.Error)
            residual
        ok (r3, out3)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r2 ←
        PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame aspis_core.state_only_prefix.r0.Error)
          residual
      ok (r2, out2)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r1 ←
      PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        Unit (core.convert.FromSame aspis_core.state_only_prefix.r0.Error)
        residual
    ok (r1, out1)

/-- [aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::{aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::Public<'a>}::public_bytes]:
    Source: 'crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs', lines 2026:8-2092:9
    Visibility: public -/
def pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
  (self : pool_v1.pair_forest_semantic_terminal.r0.Public) :
  Result (core.result.Result (alloc.vec.Vec Std.U8)
    aspis_core.state_only_prefix.r0.Error)
  := do
  let p ← pool_v1.pair_forest_semantic_terminal.r0.Public.semantic self
  match p.variant with
  | pool_v1.pair_forest_semantic_terminal.CompiledVariant.PrivateTransfer =>
    let out ← alloc.vec.Vec.push (alloc.vec.Vec.new Std.U8) 0#u8
    let s ← lift (Array.to_slice p.anchor)
    let (r, out1) ←
      pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields out s
    let cf ← PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let s1 ← lift (Array.to_slice p.nullifier)
      let (r1, out2) ←
        pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields
          out1 s1
      let cf1 ← PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        let s2 ← lift (Array.to_slice (Array.make 1#usize [ p.asset_id ]))
        let (r2, out3) ←
          pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields
            out2 s2
        let cf2 ← PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r2
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          let b := core.option.Option.is_some p.recipient
          let i ← lift (core.convert.num.FromU8Bool.from b)
          let out4 ← alloc.vec.Vec.push out3 i
          match p.recipient with
          | none =>
            let s3 ← lift (Array.to_slice p.change)
            let (r3, out5) ←
              pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields
                out4 s3
            let cf3 ← PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r3
            match cf3 with
            | core.ops.control_flow.ControlFlow.Continue _ =>
              let b1 := core.option.Option.is_some p.withdrawal_amount
              let i1 ← lift (core.convert.num.FromU8Bool.from b1)
              let out6 ← alloc.vec.Vec.push out5 i1
              match p.withdrawal_amount with
              | none =>
                let a ←
                  lift (core.num.U64.to_le_bytes
                    p.transition.live_snapshot.next_pair_index)
                let s4 ← lift (Array.to_slice a)
                let out7 ←
                  alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out6 s4
                let (r4, out8) ←
                  pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.frontier
                    out7 p.transition.live_snapshot.frontier
                let cf4 ← PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r4
                match cf4 with
                | core.ops.control_flow.ControlFlow.Continue _ =>
                  let s5 ←
                    lift (Array.to_slice
                      p.transition.candidate_afterstate.next_root)
                  let (r5, out9) ←
                    pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields
                      out8 s5
                  let cf5 ← PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r5
                  match cf5 with
                  | core.ops.control_flow.ControlFlow.Continue _ =>
                    let (r6, out10) ←
                      pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.frontier
                        out9 p.transition.candidate_afterstate.next_frontier
                    let cf6 ← PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r6
                    match cf6 with
                    | core.ops.control_flow.ControlFlow.Continue _ =>
                      let s6 ← lift (Array.to_slice p.pool)
                      let out11 ←
                        alloc.vec.Vec.extend_from_slice core.clone.CloneU8
                          out10 s6
                      let s7 ← lift (Array.to_slice p.deployment_domain)
                      let out12 ←
                        alloc.vec.Vec.extend_from_slice core.clone.CloneU8
                          out11 s7
                      let b2 := core.option.Option.is_some p.destination
                      let i2 ← lift (core.convert.num.FromU8Bool.from b2)
                      let out13 ← alloc.vec.Vec.push out12 i2
                      match p.destination with
                      | none => ok (core.result.Result.Ok out13)
                      | some destination =>
                        let s8 ← lift (Array.to_slice destination)
                        let out14 ←
                          alloc.vec.Vec.extend_from_slice core.clone.CloneU8
                            out13 s8
                        ok (core.result.Result.Ok out14)
                    | core.ops.control_flow.ControlFlow.Break residual =>
                      PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                        (alloc.vec.Vec Std.U8) (core.convert.FromSame
                        aspis_core.state_only_prefix.r0.Error) residual
                  | core.ops.control_flow.ControlFlow.Break residual =>
                    PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                      (alloc.vec.Vec Std.U8) (core.convert.FromSame
                      aspis_core.state_only_prefix.r0.Error) residual
                | core.ops.control_flow.ControlFlow.Break residual =>
                  PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                    (alloc.vec.Vec Std.U8) (core.convert.FromSame
                    aspis_core.state_only_prefix.r0.Error) residual
              | some value =>
                let s4 ← lift (Array.to_slice (Array.make 1#usize [ value ]))
                let (r4, out7) ←
                  pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields
                    out6 s4
                let cf4 ← PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r4
                match cf4 with
                | core.ops.control_flow.ControlFlow.Continue _ =>
                  let a ←
                    lift (core.num.U64.to_le_bytes
                      p.transition.live_snapshot.next_pair_index)
                  let s5 ← lift (Array.to_slice a)
                  let out8 ←
                    alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out7 s5
                  let (r5, out9) ←
                    pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.frontier
                      out8 p.transition.live_snapshot.frontier
                  let cf5 ← PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r5
                  match cf5 with
                  | core.ops.control_flow.ControlFlow.Continue _ =>
                    let s6 ←
                      lift (Array.to_slice
                        p.transition.candidate_afterstate.next_root)
                    let (r6, out10) ←
                      pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields
                        out9 s6
                    let cf6 ← PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r6
                    match cf6 with
                    | core.ops.control_flow.ControlFlow.Continue _ =>
                      let (r7, out11) ←
                        pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.frontier
                          out10 p.transition.candidate_afterstate.next_frontier
                      let cf7 ← PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r7
                      match cf7 with
                      | core.ops.control_flow.ControlFlow.Continue _ =>
                        let s7 ← lift (Array.to_slice p.pool)
                        let out12 ←
                          alloc.vec.Vec.extend_from_slice core.clone.CloneU8
                            out11 s7
                        let s8 ← lift (Array.to_slice p.deployment_domain)
                        let out13 ←
                          alloc.vec.Vec.extend_from_slice core.clone.CloneU8
                            out12 s8
                        let b2 := core.option.Option.is_some p.destination
                        let i2 ← lift (core.convert.num.FromU8Bool.from b2)
                        let out14 ← alloc.vec.Vec.push out13 i2
                        match p.destination with
                        | none => ok (core.result.Result.Ok out14)
                        | some destination =>
                          let s9 ← lift (Array.to_slice destination)
                          let out15 ←
                            alloc.vec.Vec.extend_from_slice core.clone.CloneU8
                              out14 s9
                          ok (core.result.Result.Ok out15)
                      | core.ops.control_flow.ControlFlow.Break residual =>
                        PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                          (alloc.vec.Vec Std.U8) (core.convert.FromSame
                          aspis_core.state_only_prefix.r0.Error) residual
                    | core.ops.control_flow.ControlFlow.Break residual =>
                      PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                        (alloc.vec.Vec Std.U8) (core.convert.FromSame
                        aspis_core.state_only_prefix.r0.Error) residual
                  | core.ops.control_flow.ControlFlow.Break residual =>
                    PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                      (alloc.vec.Vec Std.U8) (core.convert.FromSame
                      aspis_core.state_only_prefix.r0.Error) residual
                | core.ops.control_flow.ControlFlow.Break residual =>
                  PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                    (alloc.vec.Vec Std.U8) (core.convert.FromSame
                    aspis_core.state_only_prefix.r0.Error) residual
            | core.ops.control_flow.ControlFlow.Break residual =>
              PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                (alloc.vec.Vec Std.U8) (core.convert.FromSame
                aspis_core.state_only_prefix.r0.Error) residual
          | some value =>
            let s3 ← lift (Array.to_slice value)
            let (r3, out5) ←
              pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields
                out4 s3
            let cf3 ← PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r3
            match cf3 with
            | core.ops.control_flow.ControlFlow.Continue _ =>
              let s4 ← lift (Array.to_slice p.change)
              let (r4, out6) ←
                pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields
                  out5 s4
              let cf4 ← PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r4
              match cf4 with
              | core.ops.control_flow.ControlFlow.Continue _ =>
                let b1 := core.option.Option.is_some p.withdrawal_amount
                let i1 ← lift (core.convert.num.FromU8Bool.from b1)
                let out7 ← alloc.vec.Vec.push out6 i1
                match p.withdrawal_amount with
                | none =>
                  let a ←
                    lift (core.num.U64.to_le_bytes
                      p.transition.live_snapshot.next_pair_index)
                  let s5 ← lift (Array.to_slice a)
                  let out8 ←
                    alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out7 s5
                  let (r5, out9) ←
                    pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.frontier
                      out8 p.transition.live_snapshot.frontier
                  let cf5 ← PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r5
                  match cf5 with
                  | core.ops.control_flow.ControlFlow.Continue _ =>
                    let s6 ←
                      lift (Array.to_slice
                        p.transition.candidate_afterstate.next_root)
                    let (r6, out10) ←
                      pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields
                        out9 s6
                    let cf6 ← PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r6
                    match cf6 with
                    | core.ops.control_flow.ControlFlow.Continue _ =>
                      let (r7, out11) ←
                        pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.frontier
                          out10 p.transition.candidate_afterstate.next_frontier
                      let cf7 ← PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r7
                      match cf7 with
                      | core.ops.control_flow.ControlFlow.Continue _ =>
                        let s7 ← lift (Array.to_slice p.pool)
                        let out12 ←
                          alloc.vec.Vec.extend_from_slice core.clone.CloneU8
                            out11 s7
                        let s8 ← lift (Array.to_slice p.deployment_domain)
                        let out13 ←
                          alloc.vec.Vec.extend_from_slice core.clone.CloneU8
                            out12 s8
                        let b2 := core.option.Option.is_some p.destination
                        let i2 ← lift (core.convert.num.FromU8Bool.from b2)
                        let out14 ← alloc.vec.Vec.push out13 i2
                        match p.destination with
                        | none => ok (core.result.Result.Ok out14)
                        | some destination =>
                          let s9 ← lift (Array.to_slice destination)
                          let out15 ←
                            alloc.vec.Vec.extend_from_slice core.clone.CloneU8
                              out14 s9
                          ok (core.result.Result.Ok out15)
                      | core.ops.control_flow.ControlFlow.Break residual =>
                        PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                          (alloc.vec.Vec Std.U8) (core.convert.FromSame
                          aspis_core.state_only_prefix.r0.Error) residual
                    | core.ops.control_flow.ControlFlow.Break residual =>
                      PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                        (alloc.vec.Vec Std.U8) (core.convert.FromSame
                        aspis_core.state_only_prefix.r0.Error) residual
                  | core.ops.control_flow.ControlFlow.Break residual =>
                    PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                      (alloc.vec.Vec Std.U8) (core.convert.FromSame
                      aspis_core.state_only_prefix.r0.Error) residual
                | some value1 =>
                  let s5 ←
                    lift (Array.to_slice (Array.make 1#usize [ value1 ]))
                  let (r5, out8) ←
                    pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields
                      out7 s5
                  let cf5 ← PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r5
                  match cf5 with
                  | core.ops.control_flow.ControlFlow.Continue _ =>
                    let a ←
                      lift (core.num.U64.to_le_bytes
                        p.transition.live_snapshot.next_pair_index)
                    let s6 ← lift (Array.to_slice a)
                    let out9 ←
                      alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out8
                        s6
                    let (r6, out10) ←
                      pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.frontier
                        out9 p.transition.live_snapshot.frontier
                    let cf6 ← PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r6
                    match cf6 with
                    | core.ops.control_flow.ControlFlow.Continue _ =>
                      let s7 ←
                        lift (Array.to_slice
                          p.transition.candidate_afterstate.next_root)
                      let (r7, out11) ←
                        pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields
                          out10 s7
                      let cf7 ← PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r7
                      match cf7 with
                      | core.ops.control_flow.ControlFlow.Continue _ =>
                        let (r8, out12) ←
                          pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.frontier
                            out11
                            p.transition.candidate_afterstate.next_frontier
                        let cf8 ←
                          PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r8
                        match cf8 with
                        | core.ops.control_flow.ControlFlow.Continue _ =>
                          let s8 ← lift (Array.to_slice p.pool)
                          let out13 ←
                            alloc.vec.Vec.extend_from_slice core.clone.CloneU8
                              out12 s8
                          let s9 ← lift (Array.to_slice p.deployment_domain)
                          let out14 ←
                            alloc.vec.Vec.extend_from_slice core.clone.CloneU8
                              out13 s9
                          let b2 := core.option.Option.is_some p.destination
                          let i2 ← lift (core.convert.num.FromU8Bool.from b2)
                          let out15 ← alloc.vec.Vec.push out14 i2
                          match p.destination with
                          | none => ok (core.result.Result.Ok out15)
                          | some destination =>
                            let s10 ← lift (Array.to_slice destination)
                            let out16 ←
                              alloc.vec.Vec.extend_from_slice
                                core.clone.CloneU8 out15 s10
                            ok (core.result.Result.Ok out16)
                        | core.ops.control_flow.ControlFlow.Break residual =>
                          PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                            (alloc.vec.Vec Std.U8) (core.convert.FromSame
                            aspis_core.state_only_prefix.r0.Error) residual
                      | core.ops.control_flow.ControlFlow.Break residual =>
                        PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                          (alloc.vec.Vec Std.U8) (core.convert.FromSame
                          aspis_core.state_only_prefix.r0.Error) residual
                    | core.ops.control_flow.ControlFlow.Break residual =>
                      PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                        (alloc.vec.Vec Std.U8) (core.convert.FromSame
                        aspis_core.state_only_prefix.r0.Error) residual
                  | core.ops.control_flow.ControlFlow.Break residual =>
                    PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                      (alloc.vec.Vec Std.U8) (core.convert.FromSame
                      aspis_core.state_only_prefix.r0.Error) residual
              | core.ops.control_flow.ControlFlow.Break residual =>
                PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                  (alloc.vec.Vec Std.U8) (core.convert.FromSame
                  aspis_core.state_only_prefix.r0.Error) residual
            | core.ops.control_flow.ControlFlow.Break residual =>
              PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                (alloc.vec.Vec Std.U8) (core.convert.FromSame
                aspis_core.state_only_prefix.r0.Error) residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            (alloc.vec.Vec Std.U8) (core.convert.FromSame
            aspis_core.state_only_prefix.r0.Error) residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          (alloc.vec.Vec Std.U8) (core.convert.FromSame
          aspis_core.state_only_prefix.r0.Error) residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        (alloc.vec.Vec Std.U8) (core.convert.FromSame
        aspis_core.state_only_prefix.r0.Error) residual
  | pool_v1.pair_forest_semantic_terminal.CompiledVariant.Withdrawal =>
    let out ← alloc.vec.Vec.push (alloc.vec.Vec.new Std.U8) 1#u8
    let s ← lift (Array.to_slice p.anchor)
    let (r, out1) ←
      pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields out s
    let cf ← PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let s1 ← lift (Array.to_slice p.nullifier)
      let (r1, out2) ←
        pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields
          out1 s1
      let cf1 ← PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        let s2 ← lift (Array.to_slice (Array.make 1#usize [ p.asset_id ]))
        let (r2, out3) ←
          pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields
            out2 s2
        let cf2 ← PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r2
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          let b := core.option.Option.is_some p.recipient
          let i ← lift (core.convert.num.FromU8Bool.from b)
          let out4 ← alloc.vec.Vec.push out3 i
          match p.recipient with
          | none =>
            let s3 ← lift (Array.to_slice p.change)
            let (r3, out5) ←
              pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields
                out4 s3
            let cf3 ← PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r3
            match cf3 with
            | core.ops.control_flow.ControlFlow.Continue _ =>
              let b1 := core.option.Option.is_some p.withdrawal_amount
              let i1 ← lift (core.convert.num.FromU8Bool.from b1)
              let out6 ← alloc.vec.Vec.push out5 i1
              match p.withdrawal_amount with
              | none =>
                let a ←
                  lift (core.num.U64.to_le_bytes
                    p.transition.live_snapshot.next_pair_index)
                let s4 ← lift (Array.to_slice a)
                let out7 ←
                  alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out6 s4
                let (r4, out8) ←
                  pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.frontier
                    out7 p.transition.live_snapshot.frontier
                let cf4 ← PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r4
                match cf4 with
                | core.ops.control_flow.ControlFlow.Continue _ =>
                  let s5 ←
                    lift (Array.to_slice
                      p.transition.candidate_afterstate.next_root)
                  let (r5, out9) ←
                    pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields
                      out8 s5
                  let cf5 ← PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r5
                  match cf5 with
                  | core.ops.control_flow.ControlFlow.Continue _ =>
                    let (r6, out10) ←
                      pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.frontier
                        out9 p.transition.candidate_afterstate.next_frontier
                    let cf6 ← PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r6
                    match cf6 with
                    | core.ops.control_flow.ControlFlow.Continue _ =>
                      let s6 ← lift (Array.to_slice p.pool)
                      let out11 ←
                        alloc.vec.Vec.extend_from_slice core.clone.CloneU8
                          out10 s6
                      let s7 ← lift (Array.to_slice p.deployment_domain)
                      let out12 ←
                        alloc.vec.Vec.extend_from_slice core.clone.CloneU8
                          out11 s7
                      let b2 := core.option.Option.is_some p.destination
                      let i2 ← lift (core.convert.num.FromU8Bool.from b2)
                      let out13 ← alloc.vec.Vec.push out12 i2
                      match p.destination with
                      | none => ok (core.result.Result.Ok out13)
                      | some destination =>
                        let s8 ← lift (Array.to_slice destination)
                        let out14 ←
                          alloc.vec.Vec.extend_from_slice core.clone.CloneU8
                            out13 s8
                        ok (core.result.Result.Ok out14)
                    | core.ops.control_flow.ControlFlow.Break residual =>
                      PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                        (alloc.vec.Vec Std.U8) (core.convert.FromSame
                        aspis_core.state_only_prefix.r0.Error) residual
                  | core.ops.control_flow.ControlFlow.Break residual =>
                    PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                      (alloc.vec.Vec Std.U8) (core.convert.FromSame
                      aspis_core.state_only_prefix.r0.Error) residual
                | core.ops.control_flow.ControlFlow.Break residual =>
                  PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                    (alloc.vec.Vec Std.U8) (core.convert.FromSame
                    aspis_core.state_only_prefix.r0.Error) residual
              | some value =>
                let s4 ← lift (Array.to_slice (Array.make 1#usize [ value ]))
                let (r4, out7) ←
                  pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields
                    out6 s4
                let cf4 ← PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r4
                match cf4 with
                | core.ops.control_flow.ControlFlow.Continue _ =>
                  let a ←
                    lift (core.num.U64.to_le_bytes
                      p.transition.live_snapshot.next_pair_index)
                  let s5 ← lift (Array.to_slice a)
                  let out8 ←
                    alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out7 s5
                  let (r5, out9) ←
                    pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.frontier
                      out8 p.transition.live_snapshot.frontier
                  let cf5 ← PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r5
                  match cf5 with
                  | core.ops.control_flow.ControlFlow.Continue _ =>
                    let s6 ←
                      lift (Array.to_slice
                        p.transition.candidate_afterstate.next_root)
                    let (r6, out10) ←
                      pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields
                        out9 s6
                    let cf6 ← PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r6
                    match cf6 with
                    | core.ops.control_flow.ControlFlow.Continue _ =>
                      let (r7, out11) ←
                        pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.frontier
                          out10 p.transition.candidate_afterstate.next_frontier
                      let cf7 ← PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r7
                      match cf7 with
                      | core.ops.control_flow.ControlFlow.Continue _ =>
                        let s7 ← lift (Array.to_slice p.pool)
                        let out12 ←
                          alloc.vec.Vec.extend_from_slice core.clone.CloneU8
                            out11 s7
                        let s8 ← lift (Array.to_slice p.deployment_domain)
                        let out13 ←
                          alloc.vec.Vec.extend_from_slice core.clone.CloneU8
                            out12 s8
                        let b2 := core.option.Option.is_some p.destination
                        let i2 ← lift (core.convert.num.FromU8Bool.from b2)
                        let out14 ← alloc.vec.Vec.push out13 i2
                        match p.destination with
                        | none => ok (core.result.Result.Ok out14)
                        | some destination =>
                          let s9 ← lift (Array.to_slice destination)
                          let out15 ←
                            alloc.vec.Vec.extend_from_slice core.clone.CloneU8
                              out14 s9
                          ok (core.result.Result.Ok out15)
                      | core.ops.control_flow.ControlFlow.Break residual =>
                        PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                          (alloc.vec.Vec Std.U8) (core.convert.FromSame
                          aspis_core.state_only_prefix.r0.Error) residual
                    | core.ops.control_flow.ControlFlow.Break residual =>
                      PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                        (alloc.vec.Vec Std.U8) (core.convert.FromSame
                        aspis_core.state_only_prefix.r0.Error) residual
                  | core.ops.control_flow.ControlFlow.Break residual =>
                    PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                      (alloc.vec.Vec Std.U8) (core.convert.FromSame
                      aspis_core.state_only_prefix.r0.Error) residual
                | core.ops.control_flow.ControlFlow.Break residual =>
                  PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                    (alloc.vec.Vec Std.U8) (core.convert.FromSame
                    aspis_core.state_only_prefix.r0.Error) residual
            | core.ops.control_flow.ControlFlow.Break residual =>
              PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                (alloc.vec.Vec Std.U8) (core.convert.FromSame
                aspis_core.state_only_prefix.r0.Error) residual
          | some value =>
            let s3 ← lift (Array.to_slice value)
            let (r3, out5) ←
              pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields
                out4 s3
            let cf3 ← PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r3
            match cf3 with
            | core.ops.control_flow.ControlFlow.Continue _ =>
              let s4 ← lift (Array.to_slice p.change)
              let (r4, out6) ←
                pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields
                  out5 s4
              let cf4 ← PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r4
              match cf4 with
              | core.ops.control_flow.ControlFlow.Continue _ =>
                let b1 := core.option.Option.is_some p.withdrawal_amount
                let i1 ← lift (core.convert.num.FromU8Bool.from b1)
                let out7 ← alloc.vec.Vec.push out6 i1
                match p.withdrawal_amount with
                | none =>
                  let a ←
                    lift (core.num.U64.to_le_bytes
                      p.transition.live_snapshot.next_pair_index)
                  let s5 ← lift (Array.to_slice a)
                  let out8 ←
                    alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out7 s5
                  let (r5, out9) ←
                    pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.frontier
                      out8 p.transition.live_snapshot.frontier
                  let cf5 ← PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r5
                  match cf5 with
                  | core.ops.control_flow.ControlFlow.Continue _ =>
                    let s6 ←
                      lift (Array.to_slice
                        p.transition.candidate_afterstate.next_root)
                    let (r6, out10) ←
                      pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields
                        out9 s6
                    let cf6 ← PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r6
                    match cf6 with
                    | core.ops.control_flow.ControlFlow.Continue _ =>
                      let (r7, out11) ←
                        pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.frontier
                          out10 p.transition.candidate_afterstate.next_frontier
                      let cf7 ← PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r7
                      match cf7 with
                      | core.ops.control_flow.ControlFlow.Continue _ =>
                        let s7 ← lift (Array.to_slice p.pool)
                        let out12 ←
                          alloc.vec.Vec.extend_from_slice core.clone.CloneU8
                            out11 s7
                        let s8 ← lift (Array.to_slice p.deployment_domain)
                        let out13 ←
                          alloc.vec.Vec.extend_from_slice core.clone.CloneU8
                            out12 s8
                        let b2 := core.option.Option.is_some p.destination
                        let i2 ← lift (core.convert.num.FromU8Bool.from b2)
                        let out14 ← alloc.vec.Vec.push out13 i2
                        match p.destination with
                        | none => ok (core.result.Result.Ok out14)
                        | some destination =>
                          let s9 ← lift (Array.to_slice destination)
                          let out15 ←
                            alloc.vec.Vec.extend_from_slice core.clone.CloneU8
                              out14 s9
                          ok (core.result.Result.Ok out15)
                      | core.ops.control_flow.ControlFlow.Break residual =>
                        PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                          (alloc.vec.Vec Std.U8) (core.convert.FromSame
                          aspis_core.state_only_prefix.r0.Error) residual
                    | core.ops.control_flow.ControlFlow.Break residual =>
                      PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                        (alloc.vec.Vec Std.U8) (core.convert.FromSame
                        aspis_core.state_only_prefix.r0.Error) residual
                  | core.ops.control_flow.ControlFlow.Break residual =>
                    PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                      (alloc.vec.Vec Std.U8) (core.convert.FromSame
                      aspis_core.state_only_prefix.r0.Error) residual
                | some value1 =>
                  let s5 ←
                    lift (Array.to_slice (Array.make 1#usize [ value1 ]))
                  let (r5, out8) ←
                    pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields
                      out7 s5
                  let cf5 ← PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r5
                  match cf5 with
                  | core.ops.control_flow.ControlFlow.Continue _ =>
                    let a ←
                      lift (core.num.U64.to_le_bytes
                        p.transition.live_snapshot.next_pair_index)
                    let s6 ← lift (Array.to_slice a)
                    let out9 ←
                      alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out8
                        s6
                    let (r6, out10) ←
                      pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.frontier
                        out9 p.transition.live_snapshot.frontier
                    let cf6 ← PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r6
                    match cf6 with
                    | core.ops.control_flow.ControlFlow.Continue _ =>
                      let s7 ←
                        lift (Array.to_slice
                          p.transition.candidate_afterstate.next_root)
                      let (r7, out11) ←
                        pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields
                          out10 s7
                      let cf7 ← PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r7
                      match cf7 with
                      | core.ops.control_flow.ControlFlow.Continue _ =>
                        let (r8, out12) ←
                          pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.frontier
                            out11
                            p.transition.candidate_afterstate.next_frontier
                        let cf8 ←
                          PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r8
                        match cf8 with
                        | core.ops.control_flow.ControlFlow.Continue _ =>
                          let s8 ← lift (Array.to_slice p.pool)
                          let out13 ←
                            alloc.vec.Vec.extend_from_slice core.clone.CloneU8
                              out12 s8
                          let s9 ← lift (Array.to_slice p.deployment_domain)
                          let out14 ←
                            alloc.vec.Vec.extend_from_slice core.clone.CloneU8
                              out13 s9
                          let b2 := core.option.Option.is_some p.destination
                          let i2 ← lift (core.convert.num.FromU8Bool.from b2)
                          let out15 ← alloc.vec.Vec.push out14 i2
                          match p.destination with
                          | none => ok (core.result.Result.Ok out15)
                          | some destination =>
                            let s10 ← lift (Array.to_slice destination)
                            let out16 ←
                              alloc.vec.Vec.extend_from_slice
                                core.clone.CloneU8 out15 s10
                            ok (core.result.Result.Ok out16)
                        | core.ops.control_flow.ControlFlow.Break residual =>
                          PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                            (alloc.vec.Vec Std.U8) (core.convert.FromSame
                            aspis_core.state_only_prefix.r0.Error) residual
                      | core.ops.control_flow.ControlFlow.Break residual =>
                        PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                          (alloc.vec.Vec Std.U8) (core.convert.FromSame
                          aspis_core.state_only_prefix.r0.Error) residual
                    | core.ops.control_flow.ControlFlow.Break residual =>
                      PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                        (alloc.vec.Vec Std.U8) (core.convert.FromSame
                        aspis_core.state_only_prefix.r0.Error) residual
                  | core.ops.control_flow.ControlFlow.Break residual =>
                    PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                      (alloc.vec.Vec Std.U8) (core.convert.FromSame
                      aspis_core.state_only_prefix.r0.Error) residual
              | core.ops.control_flow.ControlFlow.Break residual =>
                PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                  (alloc.vec.Vec Std.U8) (core.convert.FromSame
                  aspis_core.state_only_prefix.r0.Error) residual
            | core.ops.control_flow.ControlFlow.Break residual =>
              PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                (alloc.vec.Vec Std.U8) (core.convert.FromSame
                aspis_core.state_only_prefix.r0.Error) residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            (alloc.vec.Vec Std.U8) (core.convert.FromSame
            aspis_core.state_only_prefix.r0.Error) residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          (alloc.vec.Vec Std.U8) (core.convert.FromSame
          aspis_core.state_only_prefix.r0.Error) residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        (alloc.vec.Vec Std.U8) (core.convert.FromSame
        aspis_core.state_only_prefix.r0.Error) residual


end AspisR1PublicPreparationPIN2

set_option maxHeartbeats 200000
#print axioms AspisR1PublicPreparationPIN2.pool_v1.pair_forest_semantic_terminal.private_public
#print axioms AspisR1PublicPreparationPIN2.pool_v1.pair_forest_semantic_terminal.withdrawal_public
#print axioms AspisR1PublicPreparationPIN2.pool_v1.pair_forest_semantic_terminal.r0.Public.semantic
#print axioms AspisR1PublicPreparationPIN2.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
