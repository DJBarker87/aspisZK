-- Generated function bodies retained from aeneas-source-op229-002.
import R1Z.PV_CB3_Afterstate
import R1Z.ProverRwFullExternalFuns
open Aeneas Aeneas.Std Result ControlFlow Error
noncomputable section
namespace PV_CB3_ShippedOp229
variable {base : ProverRwFull.ExternalTypes}
abbrev aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 :=
  ProverRwFull.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1
abbrev aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1
    (base : ProverRwFull.ExternalTypes) :=
  @ProverRwFull.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1
    (R1Z.PV_CB3_Afterstate.selectedTypes base)


/-- Trait implementation: [core::array::equality::{impl core::cmp::PartialEq<[U; N]> for [T; N]}]
    Source: '/rustc/library/core/src/array/equality.rs', lines 5:0-7:28
    Name pattern: [core::cmp::PartialEq<[@T; @N], [@U; @N]>] -/
@[reducible, rust_trait_impl "core::cmp::PartialEq<[@T; @N], [@U; @N]>"]
def Array.Insts.CoreCmpPartialEqArray {T : Type} {U : Type} (N : Std.Usize)
  (cmpPartialEqInst : core.cmp.PartialEq T U) : core.cmp.PartialEq (Array T N)
  (Array U N) := {
  eq := core.array.equality.PartialEqArray.eq cmpPartialEqInst
}

/-- [aspis_core::field::{impl core::cmp::PartialEq<aspis_core::field::M31> for aspis_core::field::M31}::eq]:
    Source: '/home/dombarker/project-offloads/codex-pv-cb3-20261026/source/crates/aspis-core/src/field.rs', lines 22:22-22:31
    Name pattern: [aspis_core::field::{core::cmp::PartialEq<aspis_core::field::M31, aspis_core::field::M31>}::eq]
    Visibility: public -/
@[rust_fun
  "aspis_core::field::{core::cmp::PartialEq<aspis_core::field::M31, aspis_core::field::M31>}::eq"]
def aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq
  (self : aspis_core.field.M31) (other : aspis_core.field.M31) :
  Result Bool
  := do
  ok (self = other)

/-- Trait implementation: [aspis_core::field::{impl core::cmp::PartialEq<aspis_core::field::M31> for aspis_core::field::M31}]
    Source: '/home/dombarker/project-offloads/codex-pv-cb3-20261026/source/crates/aspis-core/src/field.rs', lines 22:22-22:31
    Name pattern: [core::cmp::PartialEq<aspis_core::field::M31, aspis_core::field::M31>] -/
@[reducible, rust_trait_impl
  "core::cmp::PartialEq<aspis_core::field::M31, aspis_core::field::M31>"]
def aspis_core.field.M31.Insts.CoreCmpPartialEqM31 : core.cmp.PartialEq
  aspis_core.field.M31 aspis_core.field.M31 := {
  eq := aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq
}

/-- [aspis_statement::pool_v1::pair_terminal::{impl core::cmp::PartialEq<aspis_statement::pool_v1::pair_terminal::PoolV1PairVerifiedAfterstateV1> for aspis_statement::pool_v1::pair_terminal::PoolV1PairVerifiedAfterstateV1}::eq]:
    Source: '/home/dombarker/project-offloads/codex-pv-cb3-20261026/source/crates/aspis-statement/src/pool_v1/pair_terminal.rs', lines 115:29-115:38
    Name pattern: [aspis_statement::pool_v1::pair_terminal::{core::cmp::PartialEq<aspis_statement::pool_v1::pair_terminal::PoolV1PairVerifiedAfterstateV1, aspis_statement::pool_v1::pair_terminal::PoolV1PairVerifiedAfterstateV1>}::eq]
    Visibility: public -/
@[rust_fun
  "aspis_statement::pool_v1::pair_terminal::{core::cmp::PartialEq<aspis_statement::pool_v1::pair_terminal::PoolV1PairVerifiedAfterstateV1, aspis_statement::pool_v1::pair_terminal::PoolV1PairVerifiedAfterstateV1>}::eq"]
def
  aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1.Insts.CoreCmpPartialEqPoolV1PairVerifiedAfterstateV1.eq
  (self : aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1)
  (other :
  aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1) :
  Result Bool
  := do
  if self.next_pair_index = other.next_pair_index
  then
    let b ←
      core.array.equality.PartialEqArray.eq
        aspis_core.field.M31.Insts.CoreCmpPartialEqM31 self.next_root
        other.next_root
    if b
    then
      core.array.equality.PartialEqArray.eq (Array.Insts.CoreCmpPartialEqArray
        8#usize aspis_core.field.M31.Insts.CoreCmpPartialEqM31)
        self.next_frontier other.next_frontier
    else ok false
  else ok false

/-- [aspis_statement::pool_v1::pair_tree_profile::{impl core::cmp::PartialEq<aspis_statement::pool_v1::pair_tree_profile::PoolV1PairLiveSnapshotV1> for aspis_statement::pool_v1::pair_tree_profile::PoolV1PairLiveSnapshotV1}::eq]:
    Source: '/home/dombarker/project-offloads/codex-pv-cb3-20261026/source/crates/aspis-statement/src/pool_v1/pair_tree_profile.rs', lines 403:29-403:38
    Name pattern: [aspis_statement::pool_v1::pair_tree_profile::{core::cmp::PartialEq<aspis_statement::pool_v1::pair_tree_profile::PoolV1PairLiveSnapshotV1, aspis_statement::pool_v1::pair_tree_profile::PoolV1PairLiveSnapshotV1>}::eq]
    Visibility: public -/
@[rust_fun
  "aspis_statement::pool_v1::pair_tree_profile::{core::cmp::PartialEq<aspis_statement::pool_v1::pair_tree_profile::PoolV1PairLiveSnapshotV1, aspis_statement::pool_v1::pair_tree_profile::PoolV1PairLiveSnapshotV1>}::eq"]
def
  aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1.Insts.CoreCmpPartialEqPoolV1PairLiveSnapshotV1.eq
  (self : aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1)
  (other : aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1)
  :
  Result Bool
  := do
  if self.sequence = other.sequence
  then
    if self.next_pair_index = other.next_pair_index
    then
      let b ←
        core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 self.pool
          other.pool
      if b
      then
        let b1 ←
          core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8
            self.deployment_domain other.deployment_domain
        if b1
        then
          let b2 ←
            core.array.equality.PartialEqArray.eq
              aspis_core.field.M31.Insts.CoreCmpPartialEqM31 self.current_root
              other.current_root
          if b2
          then
            core.array.equality.PartialEqArray.eq
              (Array.Insts.CoreCmpPartialEqArray 8#usize
              aspis_core.field.M31.Insts.CoreCmpPartialEqM31) self.frontier
              other.frontier
          else ok false
        else ok false
      else ok false
    else ok false
  else ok false

/-- [aspis_statement::pool_v1::pair_tree_profile::{impl core::cmp::PartialEq<aspis_statement::pool_v1::pair_tree_profile::PoolV1PairLatePublicStatementV1> for aspis_statement::pool_v1::pair_tree_profile::PoolV1PairLatePublicStatementV1}::eq]:
    Source: '/home/dombarker/project-offloads/codex-pv-cb3-20261026/source/crates/aspis-statement/src/pool_v1/pair_tree_profile.rs', lines 413:29-413:38
    Name pattern: [aspis_statement::pool_v1::pair_tree_profile::{core::cmp::PartialEq<aspis_statement::pool_v1::pair_tree_profile::PoolV1PairLatePublicStatementV1, aspis_statement::pool_v1::pair_tree_profile::PoolV1PairLatePublicStatementV1>}::eq]
    Visibility: public -/
@[rust_fun
  "aspis_statement::pool_v1::pair_tree_profile::{core::cmp::PartialEq<aspis_statement::pool_v1::pair_tree_profile::PoolV1PairLatePublicStatementV1, aspis_statement::pool_v1::pair_tree_profile::PoolV1PairLatePublicStatementV1>}::eq"]
def
  aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1.Insts.CoreCmpPartialEqPoolV1PairLatePublicStatementV1.eq
  (self :
  (aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 base))
  (other :
  (aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 base)) :
  Result Bool
  := do
  let b ←
    aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1.Insts.CoreCmpPartialEqPoolV1PairLiveSnapshotV1.eq
      (@ProverRwFull.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1.live_snapshot (R1Z.PV_CB3_Afterstate.selectedTypes base) self) (@ProverRwFull.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1.live_snapshot (R1Z.PV_CB3_Afterstate.selectedTypes base) other)
  if b
  then
    aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1.Insts.CoreCmpPartialEqPoolV1PairVerifiedAfterstateV1.eq
      (@ProverRwFull.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1.candidate_afterstate (R1Z.PV_CB3_Afterstate.selectedTypes base) self) (@ProverRwFull.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1.candidate_afterstate (R1Z.PV_CB3_Afterstate.selectedTypes base) other)
  else ok false

/-- Trait implementation: [aspis_statement::pool_v1::pair_tree_profile::{impl core::cmp::PartialEq<aspis_statement::pool_v1::pair_tree_profile::PoolV1PairLatePublicStatementV1> for aspis_statement::pool_v1::pair_tree_profile::PoolV1PairLatePublicStatementV1}]
    Source: '/home/dombarker/project-offloads/codex-pv-cb3-20261026/source/crates/aspis-statement/src/pool_v1/pair_tree_profile.rs', lines 413:29-413:38
    Name pattern: [core::cmp::PartialEq<aspis_statement::pool_v1::pair_tree_profile::PoolV1PairLatePublicStatementV1, aspis_statement::pool_v1::pair_tree_profile::PoolV1PairLatePublicStatementV1>] -/
@[reducible, rust_trait_impl
  "core::cmp::PartialEq<aspis_statement::pool_v1::pair_tree_profile::PoolV1PairLatePublicStatementV1, aspis_statement::pool_v1::pair_tree_profile::PoolV1PairLatePublicStatementV1>"]
def
  aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1.Insts.CoreCmpPartialEqPoolV1PairLatePublicStatementV1
  : core.cmp.PartialEq
  (aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 base)
  (aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 base)
  := {
  eq :=
    aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1.Insts.CoreCmpPartialEqPoolV1PairLatePublicStatementV1.eq
}

/-- [pv_cb3_source::statement_eq]:
    Source: 'lib.rs', lines 40:0-42:1
    Visibility: public -/
def statement_eq
  (a :
  (aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 base))
  (b :
  (aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 base)) :
  Result Bool
  := do
  aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1.Insts.CoreCmpPartialEqPoolV1PairLatePublicStatementV1.eq
    a b

end PV_CB3_ShippedOp229

namespace R1Z.PV_CB3_Op229Source
open ProverRwFull
set_option autoImplicit false
@[reducible] def selected (base : ExternalTypes)
    (ops : @ExternalFuns (PV_CB3_Afterstate.selectedTypes base)) :
    @ExternalFuns (PV_CB3_Afterstate.selectedTypes base) :=
  letI : ExternalTypes := PV_CB3_Afterstate.selectedTypes base
  {ops with op229 := PV_CB3_ShippedOp229.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1.Insts.CoreCmpPartialEqPoolV1PairLatePublicStatementV1.eq (base := base)}

/-- Complete source equation at the concrete extracted afterstate carrier. -/
theorem op229_source (base : ExternalTypes)
    (ops : @ExternalFuns (PV_CB3_Afterstate.selectedTypes base))
    (a b : @aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 (PV_CB3_Afterstate.selectedTypes base)) :
    @ExternalFuns.op229 (PV_CB3_Afterstate.selectedTypes base) (selected base ops) a b =
      PV_CB3_ShippedOp229.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1.Insts.CoreCmpPartialEqPoolV1PairLatePublicStatementV1.eq a b := rfl
#print axioms op229_source
end R1Z.PV_CB3_Op229Source
