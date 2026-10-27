-- Frozen changed external adapter: fallback now calls the extracted fallback owner.
import Aeneas
import AspisR1CircleSampleWrapper.Types
import AspisR72Sampler.Funs
import AspisR1PublicPreparation.Funs
import AspisR1CircleFallback.Funs
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
open AspisR1CircleSampleWrapper

/-- Closure alias emitted in generated Types; kept here so the selected named Types OLean can be reused. -/
@[reducible]
def sampler.circle_sample.closure := r0_transcript.CircleRow

/-- Lean model of Rust's `Result::unwrap_or_else`: return the `Ok` payload,
or call the supplied `FnOnce` exactly once with the `Err` payload. -/
@[rust_fun "core::result::{core::result::Result<T, E>}::unwrap_or_else"]
def core.result.Result.unwrap_or_else
    {T E F : Type}
    (inst : core.ops.function.FnOnce F E T)
    (r : core.result.Result T E) (f : F) : Result T :=
  match r with
  | .Ok x => Result.ok x
  | .Err e => inst.call_once f e

/-- Explicit record-layout map from the fallback extraction to the wrapper owner. -/
def fromFallbackCM (x : AspisR1CircleFallback.field.CM31) : field.CM31 := ⟨x.a, x.b⟩
def fromFallbackQM (x : AspisR1CircleFallback.field.QM31) : field.QM31 :=
  ⟨fromFallbackCM x.c0, fromFallbackCM x.c1⟩
def fromFallbackPoint (x : AspisR1CircleFallback.circle.SecureCirclePoint) :
    circle.SecureCirclePoint := ⟨fromFallbackQM x.x, fromFallbackQM x.y⟩

/-- Secure mapper adapted through the selected R72 representation owner. -/
def toR72CM (x : field.CM31) : AspisR72Sampler.field.CM31 := ⟨x.a, x.b⟩
def toR72QM (x : field.QM31) : AspisR72Sampler.field.QM31 :=
  ⟨toR72CM x.c0, toR72CM x.c1⟩
def fromR72CM (x : AspisR72Sampler.field.CM31) : field.CM31 := ⟨x.a, x.b⟩
def fromR72QM (x : AspisR72Sampler.field.QM31) : field.QM31 :=
  ⟨fromR72CM x.c0, fromR72CM x.c1⟩
def fromR72Point (x : AspisR72Sampler.circle.SecureCirclePoint) : circle.SecureCirclePoint :=
  ⟨fromR72QM x.x, fromR72QM x.y⟩
def fromR72Error : AspisR72Sampler.circle.CirclePointError → circle.CirclePointError
  | .SingularParameter => .SingularParameter
  | .ParameterInCm31Subfield => .ParameterInCm31Subfield

def circle.secure_ood_circle_point_from_parameter (q : field.QM31) :
    Result (core.result.Result circle.SecureCirclePoint circle.CirclePointError) := do
  let r ← AspisR72Sampler.circle.secure_ood_circle_point_from_parameter (toR72QM q)
  match r with
  | .Ok p => ok (.Ok (fromR72Point p))
  | .Err e => ok (.Err (fromR72Error e))

/-- This replaces the former opaque axiom with the exact extracted fallback function. -/
def transcript.circle_fallback_point (i : Std.Usize) : Result circle.SecureCirclePoint := do
  let p ← AspisR1CircleFallback.transcript.circle_fallback_point i
  ok (fromFallbackPoint p)

/-- Public sampler adapted through the retained public-preparation implementation. -/
def fromPublicQM (q : AspisR1PublicPreparation.aspis_core.field.QM31) : field.QM31 :=
  ⟨⟨q.c0.a, q.c0.b⟩, ⟨q.c1.a, q.c1.b⟩⟩
def sampler.qm31_sample (block : Array Std.U8 32#usize) : Result field.QM31 := do
  let q ← AspisR1PublicPreparation.sampler.qm31_sample block
  ok (fromPublicQM q)
