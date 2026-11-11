-- PIN2 NEW GATE for r1_semantic::public_transcript at source c7593d23fdc56fcee9a9df1628d5f63b52ac7a95 (PIN2 pin; text of r1_semantic.rs unchanged since 4bb3b3f).
-- Emission PCXU_E003: Charon 454586e9 + Aeneas 0d21a9ec (second tool version, same as PCXQ_E001), overflow-checks ON, features private-leaf-salts,optimized-terminal,program-build,
-- cargo --jobs 4 / CARGO_BUILD_JOBS=4, rustc -Zthreads=1, identity by class receipt PCWE_E003, roots public_transcript + r0 Public::public_bytes.
-- Raw emission sha256: Types.lean f895ed757d94a793e9eaa608897208638cd465fa973caf61c5e34ac08b2170f9 Funs.lean 6c221116a673a02072ee4f55991ea21dc24febb32d15030c60149b85e584c099
-- Composes with PIN2_NEWGATE_r0 (import) in the same namespace AspisR1PublicPreparationPIN2; declarations identical to those in PIN2_NEWGATE_r0 are dropped (listed in PCXU_NEWGATE_DECLS.json).
-- Built by PCXU_mk_newgate.py. Contains no placeholder proof and no axiom.
import Aeneas
import PIN2_NEWGATE_r0
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option maxRecDepth 2048

/- Aeneas-generated default heartbeat budget for the emitted definitions (no theorem below this line except the audit prints). -/
set_option maxHeartbeats 1000000

/- New-library model (Aeneas 0d21a9ec, backends/lean/Aeneas/Std/Core/CoreResult.lean, `core.result.Result.map_err`, copied verbatim): the L187 closure's Aeneas library lacks it.
   Same treatment as the branch/from_residual models in PIN2_NEWGATE_r0 (trust row HM-C, Option/Result). -/
namespace PCWN_NewLib
open Aeneas.Std
def core.result.Result.map_err
  {T E F O : Type _} (fnOnce : core.ops.function.FnOnce O E F)
  (x : core.result.Result T E) (f : O) :
  Std.Result (core.result.Result T F) :=
  match x with
  | .Ok value => ok (.Ok value)
  | .Err error => do
      let mapped ← fnOnce.call_once f error
      ok (.Err mapped)
end PCWN_NewLib

namespace AspisR1PublicPreparationPIN2

/-- Trait declaration: [aspis_core::digest::Digest32]
    Source: 'crates/aspis-core/src/digest.rs', lines 6:0-6:24
    Name pattern: [aspis_core::digest::Digest32]
    Visibility: public -/
@[rust_trait "aspis_core::digest::Digest32"
  (parentClauses := ["coremarkerCopyInst"])]
structure aspis_core.digest.Digest32 (Self : Type _) where
  coremarkerCopyInst : core.marker.Copy Self
  digest : Self → Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)

/-- [aspis_r1_cost_probe::r1_wire::{aspis_r1_cost_probe::r1_wire::SemanticTranscript<H>}::new::{closure}]
    Source: 'crates/aspis-r1-cost-probe/src/r1_wire.rs', lines 180:63-180:80 -/
@[reducible]
def r1_wire.SemanticTranscript.new.closure (H : Type _) := Unit

/-- [aspis_r1_cost_probe::r1_wire::Error]
    Source: 'crates/aspis-r1-cost-probe/src/r1_wire.rs', lines 24:0-36:1
    Visibility: public -/
inductive r1_wire.Error where
| Allocation : r1_wire.Error
| RowOrder : Std.U8 → Std.U8 → r1_wire.Error
| InvalidRow : r1_wire.Error
| Tag : Std.U8 → r1_wire.Error
| Length : Std.U8 → r1_wire.Error
| NonCanonical : Std.U8 → Std.Usize → r1_wire.Error
| Boundary : Std.Usize → r1_wire.Error
| Terminal : r1_wire.Error
| EqualCirclePoints : r1_wire.Error
| TrailingBytes : r1_wire.Error
| Public : r1_wire.Error

/- PIN2 W3c (overlay copy): `@[discriminant isize]` replaced by the definition the
   attribute generates plus an explicitly named instance inside this namespace, so the
   instance no longer lands at top level as `instDiscriminant<Ty>Isize` (clash with the
   gate module AspisR1FinishRelationCurrent.Types). Discriminant values: 0..n-1 in
   constructor order, as the attribute assigns. -/
def r1_wire.Error.read_discriminant (x : r1_wire.Error) : Std.Isize :=
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

instance instDiscriminant_PIN2_r1_WireError_Isize : Aeneas.Std.Discriminant r1_wire.Error Std.Isize where
  read_discriminant := r1_wire.Error.read_discriminant

/-- [aspis_r1_cost_probe::r1_wire::SemanticTranscript]
    Source: 'crates/aspis-r1-cost-probe/src/r1_wire.rs', lines 172:0-176:1
    Visibility: public -/
structure r1_wire.SemanticTranscript (H : Type _) where
  state : Array Std.U8 32#usize
  hash : H
  next_row : Std.U8

/-- [aspis_r1_cost_probe::r1_semantic::public_transcript::{closure}]
    Source: 'crates/aspis-r1-cost-probe/src/r1_semantic.rs', lines 70:39-70:56 -/
@[reducible]
def r1_semantic.public_transcript.closure (H : Type _) := Unit

/-- [aspis_r1_cost_probe::r1_wire::{aspis_r1_cost_probe::r1_wire::SemanticTranscript<H>}::new::{impl core::ops::function::FnOnce<(core::num::error::TryFromIntError,), aspis_r1_cost_probe::r1_wire::Error> for aspis_r1_cost_probe::r1_wire::{aspis_r1_cost_probe::r1_wire::SemanticTranscript<H>[TraitClause0]}::new::{closure}<H>}::call_once]:
    Source: 'crates/aspis-r1-cost-probe/src/r1_wire.rs', lines 180:63-180:80 -/
def
  r1_wire.SemanticTranscript.new.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromIntErrorError.call_once
  {H : Type _} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (c : r1_wire.SemanticTranscript.new.closure H)
  (tupled_args : core.num.error.TryFromIntError) :
  Result r1_wire.Error
  := do
  ok r1_wire.Error.Public

/-- Trait implementation: [aspis_r1_cost_probe::r1_wire::{aspis_r1_cost_probe::r1_wire::SemanticTranscript<H>}::new::{impl core::ops::function::FnOnce<(core::num::error::TryFromIntError,), aspis_r1_cost_probe::r1_wire::Error> for aspis_r1_cost_probe::r1_wire::{aspis_r1_cost_probe::r1_wire::SemanticTranscript<H>[TraitClause0]}::new::{closure}<H>}]
    Source: 'crates/aspis-r1-cost-probe/src/r1_wire.rs', lines 180:63-180:80 -/
@[reducible]
def
  r1_wire.SemanticTranscript.new.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromIntErrorError
  {H : Type _} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H) :
  core.ops.function.FnOnce (r1_wire.SemanticTranscript.new.closure H)
  core.num.error.TryFromIntError r1_wire.Error := {
  call_once :=
    r1_wire.SemanticTranscript.new.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromIntErrorError.call_once
    aspis_coredigestDigest32Inst
}

/-- [aspis_r1_cost_probe::r1_wire::DOMAIN]
    Source: 'crates/aspis-r1-cost-probe/src/r1_wire.rs', lines 12:0-12:68
    Visibility: public -/
@[global_simps, irreducible]
def r1_wire.DOMAIN : Slice Std.U8 :=
  Array.to_slice
    (Array.make 38#usize [
      85#u8, 78#u8, 80#u8, 82#u8, 79#u8, 86#u8, 69#u8, 68#u8, 58#u8, 82#u8,
      49#u8, 58#u8, 80#u8, 82#u8, 73#u8, 86#u8, 65#u8, 84#u8, 69#u8, 45#u8,
      83#u8, 65#u8, 76#u8, 84#u8, 69#u8, 68#u8, 58#u8, 83#u8, 69#u8, 77#u8,
      65#u8, 78#u8, 84#u8, 73#u8, 67#u8, 58#u8, 80#u8, 51#u8
      ])

/-- [aspis_r1_cost_probe::r1_wire::{aspis_r1_cost_probe::r1_wire::SemanticTranscript<H>}::new]:
    Source: 'crates/aspis-r1-cost-probe/src/r1_wire.rs', lines 179:4-186:5
    Visibility: public -/
def r1_wire.SemanticTranscript.new
  {H : Type _} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (hash : H) (public_bytes : Slice Std.U8) (c1_root : Array Std.U8 32#usize) :
  Result (core.result.Result (r1_wire.SemanticTranscript H) r1_wire.Error)
  := do
  let i := Slice.len public_bytes
  let r ← core.convert.num.ptr_try_from_impls.TryFromU32Usize.try_from i
  let r1 ←
    PCWN_NewLib.core.result.Result.map_err
      (r1_wire.SemanticTranscript.new.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromIntErrorError
      aspis_coredigestDigest32Inst) r ()
  let cf ← PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r1
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let s ← lift (Array.to_slice (Array.make 1#usize [ 0#u8 ]))
    let a ← lift (core.num.U32.to_le_bytes val)
    let s1 ← lift (Array.to_slice a)
    let s2 ← lift (Array.to_slice c1_root)
    let s3 ←
      lift (Array.to_slice
        (Array.make 5#usize [ r1_wire.DOMAIN, s, s1, public_bytes, s2 ]))
    let a1 ← aspis_coredigestDigest32Inst.digest hash s3
    ok (core.result.Result.Ok { state := a1, hash, next_row := 0#u8 })
  | core.ops.control_flow.ControlFlow.Break residual =>
    PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
      (r1_wire.SemanticTranscript H) (core.convert.FromSame r1_wire.Error)
      residual

/-- [aspis_r1_cost_probe::r1_semantic::public_transcript::{impl core::ops::function::FnOnce<(aspis_core::state_only_prefix::r0::Error,), aspis_r1_cost_probe::r1_wire::Error> for aspis_r1_cost_probe::r1_semantic::public_transcript::{closure}<H>}::call_once]:
    Source: 'crates/aspis-r1-cost-probe/src/r1_semantic.rs', lines 70:39-70:56 -/
def
  r1_semantic.public_transcript.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once
  {H : Type _} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (c : r1_semantic.public_transcript.closure H)
  (tupled_args : aspis_core.state_only_prefix.r0.Error) :
  Result r1_wire.Error
  := do
  ok r1_wire.Error.Public

/-- Trait implementation: [aspis_r1_cost_probe::r1_semantic::public_transcript::{impl core::ops::function::FnOnce<(aspis_core::state_only_prefix::r0::Error,), aspis_r1_cost_probe::r1_wire::Error> for aspis_r1_cost_probe::r1_semantic::public_transcript::{closure}<H>}]
    Source: 'crates/aspis-r1-cost-probe/src/r1_semantic.rs', lines 70:39-70:56 -/
@[reducible]
def
  r1_semantic.public_transcript.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError
  {H : Type _} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H) :
  core.ops.function.FnOnce (r1_semantic.public_transcript.closure H)
  aspis_core.state_only_prefix.r0.Error r1_wire.Error := {
  call_once :=
    r1_semantic.public_transcript.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once
    aspis_coredigestDigest32Inst
}

/-- [aspis_r1_cost_probe::r1_semantic::public_transcript]:
    Source: 'crates/aspis-r1-cost-probe/src/r1_semantic.rs', lines 63:0-73:1
    Visibility: public -/
def r1_semantic.public_transcript
  {H : Type _} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  («public» :
  pool_v1.pair_forest_semantic_terminal.r0.Public) (hash : H)
  (c1_root : Array Std.U8 32#usize) :
  Result (core.result.Result (r1_wire.SemanticTranscript H) r1_wire.Error)
  := do
  let r ←
    pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
      «public»
  let r1 ←
    PCWN_NewLib.core.result.Result.map_err
      (r1_semantic.public_transcript.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError
      aspis_coredigestDigest32Inst) r ()
  let cf ← PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r1
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let s := alloc.vec.Vec.deref val
    r1_wire.SemanticTranscript.new aspis_coredigestDigest32Inst hash s c1_root
  | core.ops.control_flow.ControlFlow.Break residual =>
    PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
      (r1_wire.SemanticTranscript H) (core.convert.FromSame r1_wire.Error)
      residual

end AspisR1PublicPreparationPIN2

set_option maxHeartbeats 200000
#print axioms AspisR1PublicPreparationPIN2.r1_semantic.public_transcript
#print axioms AspisR1PublicPreparationPIN2.r1_wire.SemanticTranscript.new
