import R1Z.PV_RE_NoCatchGenerator
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_NoCatchSuffix020
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_semantic.lift`.
Recursive calls remain the original extracted calls. -/
def continueAfter (x : aspis_core.field.M31) (out : Payload (aspis_core.field.CM31.from_m31 x)) : Result aspis_core.field.QM31 := do
  let c := out
  aspis_core.field.QM31.from_cm31 c


end R1Z.PV_RE_NoCatchSuffix020
pv_no_catch_binds ProverRwFull.host_semantic.lift
pv_no_catch_binds R1Z.PV_RE_NoCatchSuffix020.continueAfter

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_NoCatchSuffix021
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_semantic.zc_rows`.
Recursive calls remain the original extracted calls. -/
def continueAfter {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H) (transcript : host_wire.SemanticTranscript H) (bytes : alloc.vec.Vec Std.U8) (out : Payload (aspis_core.field.QM31.ZERO)) : Result ((core.result.Result (Array aspis_core.field.QM31 10#usize)
    r1_wire.Error) × (host_wire.SemanticTranscript H) × (alloc.vec.Vec
    Std.U8)) := do
  let q := out
  let zc := Array.repeat 10#usize q
  let (transcript1, bytes1, zc1, pending_return) ←
    host_semantic.zc_rows_loop aspis_coredigestDigest32Inst transcript bytes zc
      0#usize
  match pending_return with
  | none => ok (core.result.Result.Ok zc1, transcript1, bytes1)
  | some r => ok (r, transcript1, bytes1)


end R1Z.PV_RE_NoCatchSuffix021
pv_no_catch_binds ProverRwFull.host_semantic.zc_rows
pv_no_catch_binds R1Z.PV_RE_NoCatchSuffix021.continueAfter
