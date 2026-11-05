import VTop_Model
set_option autoImplicit false
noncomputable section
namespace NHT_Constants
open Aeneas Aeneas.Std Result VTop_Stages
/-- [core::option::{core::option::Option<T>}::ok_or]:
    Source: '/rustc/library/core/src/option.rs', lines 1334:4-1334:73
    Name pattern: [core::option::{core::option::Option<@T>}::ok_or]
    Visibility: public -/
@[rust_fun "core::option::{core::option::Option<@T>}::ok_or"]
def core.option.Option.ok_or
  {T : Type} {E : Type} (self : Option T) (err : E) :
  Result (core.result.Result T E)
  := do
  match self with
  | none => ok (core.result.Result.Err err)
  | some v => ok (core.result.Result.Ok v)

/-- [aspis_r1_cost_probe::compact::FINAL_LEN]
    Source: 'crates/aspis-r1-cost-probe/src/compact.rs', lines 45:0-45:32
    Visibility: public -/
@[global_simps, irreducible] def compact.FINAL_LEN : Std.Usize := 64#usize

/-- [aspis_r1_cost_probe::compact::HEADER]
    Source: 'crates/aspis-r1-cost-probe/src/compact.rs', lines 26:0-26:29
    Visibility: public -/
@[global_simps, irreducible] def compact.HEADER : Std.Usize := 16#usize

/-- [aspis_r1_cost_probe::compact::OFF_SEMANTIC]
    Source: 'crates/aspis-r1-cost-probe/src/compact.rs', lines 38:0-38:39
    Visibility: public -/
@[global_simps, irreducible]
def compact.OFF_SEMANTIC : Std.Usize := compact.HEADER

/-- [aspis_r1_cost_probe::compact::SEMANTIC_COMPACT_VALUES]
    Source: 'crates/aspis-r1-cost-probe/src/compact.rs', lines 33:0-33:72
    Visibility: public -/
@[global_simps, irreducible]
def compact.SEMANTIC_COMPACT_VALUES : Result Std.Usize := do
  let i ← 10#usize * 28#usize
  let i1 ← 1#usize + i
  let i2 ← 87#usize + 29#usize
  let i3 ← i1 + i2
  i3 + 29#usize

/-- [aspis_r1_cost_probe::verifier::SEMANTIC_BYTES]
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 8:0-8:43
    Visibility: public -/
@[global_simps, irreducible]
def verifier.SEMANTIC_BYTES : Result Std.Usize := do
  let i ← 29#usize * 32#usize
  12903#usize + i

/-- [aspis_r1_cost_probe::compact::LOGICAL_SEMANTIC]
    Source: 'crates/aspis-r1-cost-probe/src/compact.rs', lines 31:0-31:68
    Visibility: public -/
@[global_simps, irreducible]
def compact.LOGICAL_SEMANTIC : Result Std.Usize := verifier.SEMANTIC_BYTES

/-- [aspis_r1_cost_probe::compact::COMPACT_SEMANTIC]
    Source: 'crates/aspis-r1-cost-probe/src/compact.rs', lines 34:0-34:84
    Visibility: public -/
@[global_simps, irreducible]
def compact.COMPACT_SEMANTIC : Result Std.Usize := do
  let i ← compact.SEMANTIC_COMPACT_VALUES
  let i1 ← 16#usize * i
  let i2 ← compact.LOGICAL_SEMANTIC
  i2 - i1

/-- [aspis_r1_cost_probe::compact::OFF_Y1]
    Source: 'crates/aspis-r1-cost-probe/src/compact.rs', lines 39:0-39:58
    Visibility: public -/
@[global_simps, irreducible]
def compact.OFF_Y1 : Result Std.Usize := do
  let i ← compact.COMPACT_SEMANTIC
  compact.OFF_SEMANTIC + i

/-- [aspis_r1_cost_probe::compact::COMPACT_Y1]
    Source: 'crates/aspis-r1-cost-probe/src/compact.rs', lines 35:0-35:38
    Visibility: public -/
@[global_simps, irreducible]
def compact.COMPACT_Y1 : Result Std.Usize := 29#usize * 16#usize

/-- [aspis_r1_cost_probe::compact::OFF_INACTIVE]
    Source: 'crates/aspis-r1-cost-probe/src/compact.rs', lines 40:0-40:52
    Visibility: public -/
@[global_simps, irreducible]
def compact.OFF_INACTIVE : Result Std.Usize := do
  let i ← compact.OFF_Y1
  let i1 ← compact.COMPACT_Y1
  i + i1

/-- [aspis_r1_cost_probe::compact::OFF_ROUND0]
    Source: 'crates/aspis-r1-cost-probe/src/compact.rs', lines 41:0-41:48
    Visibility: public -/
@[global_simps, irreducible]
def compact.OFF_ROUND0 : Result Std.Usize := do
  let i ← compact.OFF_INACTIVE
  i + 32#usize

/-- [aspis_r1_cost_probe::compact::OFF_FOLDED_ROOT]
    Source: 'crates/aspis-r1-cost-probe/src/compact.rs', lines 42:0-42:52
    Visibility: public -/
@[global_simps, irreducible]
def compact.OFF_FOLDED_ROOT : Result Std.Usize := do
  let i ← compact.OFF_ROUND0
  i + 224#usize

/-- [aspis_r1_cost_probe::compact::OFF_ROUND1]
    Source: 'crates/aspis-r1-cost-probe/src/compact.rs', lines 43:0-43:51
    Visibility: public -/
@[global_simps, irreducible]
def compact.OFF_ROUND1 : Result Std.Usize := do
  let i ← compact.OFF_FOLDED_ROOT
  i + 32#usize

/-- [aspis_r1_cost_probe::compact::OFF_FINAL]
    Source: 'crates/aspis-r1-cost-probe/src/compact.rs', lines 44:0-44:46
    Visibility: public -/
@[global_simps, irreducible]
def compact.OFF_FINAL : Result Std.Usize := do
  let i ← compact.OFF_ROUND1
  i + 224#usize

/-- [aspis_r1_cost_probe::compact::OFF_OPENINGS]
    Source: 'crates/aspis-r1-cost-probe/src/compact.rs', lines 46:0-46:59
    Visibility: public -/
@[global_simps, irreducible]
def compact.OFF_OPENINGS : Result Std.Usize := do
  let i ← compact.FINAL_LEN * 32#usize
  let i1 ← compact.OFF_FINAL
  i1 + i

/-- [aspis_r1_cost_probe::compact::SPLIT]
    Source: 'crates/aspis-r1-cost-probe/src/compact.rs', lines 27:0-27:28
    Visibility: public -/
@[global_simps, irreducible] def compact.SPLIT : Std.Usize := 10#usize


end NHT_Constants
