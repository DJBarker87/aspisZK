import Aeneas
import NID_ResumeEmissionTypes
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
noncomputable section
namespace NJC_ReaderEmission
def core.option.Option.ok_or {T Err : Type} (self : Option T) (err : Err) :
 Result (core.result.Result T Err) :=
 match self with
 | none => ok (.Err err)
 | some value => ok (.Ok value)

abbrev verifier.Reader := NID_ResumeEmission.verifier.Reader
abbrev verifier.Error := NID_ResumeEmission.verifier.Error
abbrev aspis_core.field.QM31 := NID_ResumeEmission.aspis_core.field.QM31
abbrev aspis_core.field.wide_exact.WideExact := NID_ResumeEmission.aspis_core.field.wide_exact.WideExact
/-- [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::Reader<'a>}::raw]:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 344:4-344:116 -/
def verifier.Reader.raw
  (N : Std.Usize)
  (unwrap : core.result.Result (Array U8 N) core.array.TryFromSliceError → Result (Array U8 N))
  (self : verifier.Reader) :
  Result ((Array Std.U8 N) × verifier.Reader)
  := do
  let i ← self.«at» + N
  let s ←
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice
      Std.U8) self.bytes { start := self.«at», «end» := i }
  let r ← core.array.TryFromArrayCopySlice.try_from N core.marker.CopyU8 s
  let b ← unwrap r
  ok (b, { self with «at» := i })

/-- [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::Reader<'a>}::k]:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 347:4-347:98 -/
def verifier.Reader.k
  (unwrap : core.result.Result (Array U8 16#usize) core.array.TryFromSliceError → Result (Array U8 16#usize))
  (parseK : Slice U8 → Result (Option aspis_core.field.QM31))
  (self : verifier.Reader) :
  Result ((core.result.Result aspis_core.field.QM31 verifier.Error) ×
    verifier.Reader)
  := do
  let (a, self1) ← verifier.Reader.raw 16#usize unwrap self
  let s ← lift (Array.to_slice a)
  let o ← parseK s
  let r ← core.option.Option.ok_or o NID_ResumeEmission.verifier.Error.Checkpoint
  ok (r, self1)

/-- [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::Reader<'a>}::e]:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 345:4-345:98 -/
def verifier.Reader.e
  (unwrap : core.result.Result (Array U8 32#usize) core.array.TryFromSliceError → Result (Array U8 32#usize))
  (parseE : Slice U8 → Result (Option aspis_core.field.wide_exact.WideExact))
  (self : verifier.Reader) :
  Result ((core.result.Result aspis_core.field.wide_exact.WideExact
    verifier.Error) × verifier.Reader)
  := do
  let (a, self1) ← verifier.Reader.raw 32#usize unwrap self
  let s ← lift (Array.to_slice a)
  let o ← parseE s
  let r ← core.option.Option.ok_or o NID_ResumeEmission.verifier.Error.Checkpoint
  ok (r, self1)


end NJC_ReaderEmission
