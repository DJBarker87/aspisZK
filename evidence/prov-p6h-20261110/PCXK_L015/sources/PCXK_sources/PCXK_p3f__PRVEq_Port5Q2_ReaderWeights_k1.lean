-- PCVF_ item 2 (parametric record Port5Q2_ReaderWeights: ReadK parameter + hand IterMut model). Statements: fresh = gate.
-- Fresh text: PCQD_E034 emission (prov-p1g-20261109/PCQD_E034_emitted/raw/PCQD_d11b, Aeneas b59d5188-extended, overflow ON),
-- declarations Reader.raw, Reader.k, read_checkpoint_weights{,_loop,_loop.body} (+ ok_or). Types (M31, CM31, QM31, Error, Reader) are read as the
-- gate's declarations of the same name (same structure text; only the discriminant attribute differs). Externals of the emission
-- (axioms there): QM31.from_le_bytes and MutAVec..IterMut.into_iter (at A := Global) are fields of `Ext`.
-- RESULT CLASS: CONDITIONAL_ON_BINDING. The gate takes `read : ReadK` and uses the hand model `intoIter`; the equality is
-- at read := fresh Reader.k and with the Vec-IterMut external bound to the hand model (hypothesis hInto: the core slice iterator model).
import Aeneas
import Port5Q2_ReaderWeights
open Aeneas Aeneas.Std Result ControlFlow Error AspisR1Stage2
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace AspisR1.Port5Q2_ReaderWeights
namespace PRVFresh_k1

structure Ext where
  from_le_bytes : (Slice Std.U8) → Result (Option aspis_core.field.QM31)
  into_iter : (alloc.vec.Vec aspis_core.field.QM31) →
    Result ((core.slice.iter.IterMut aspis_core.field.QM31) × (core.slice.iter.IterMut aspis_core.field.QM31 → alloc.vec.Vec aspis_core.field.QM31))

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

/-- [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::Reader<'a>}::raw]:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 344:4-344:116 -/
def verifier.Reader.raw
  (N : Std.Usize) (self : verifier.Reader) :
  Result ((Array Std.U8 N) × verifier.Reader)
  := do
  let i ← self.«at» + N
  let s ←
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice
      Std.U8) self.bytes { start := self.«at», «end» := i }
  let r ← core.array.TryFromArrayCopySlice.try_from N core.marker.CopyU8 s
  let b ← core.result.Result.unwrap core.fmt.DebugTryFromSliceError r
  ok (b, { self with «at» := i })

/-- [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::Reader<'a>}::k]:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 347:4-347:98 -/
def verifier.Reader.k (x : Ext)
  (self : verifier.Reader) :
  Result ((core.result.Result aspis_core.field.QM31 verifier.Error) ×
    verifier.Reader)
  := do
  let (a, self1) ← verifier.Reader.raw 16#usize self
  let s ← lift (Array.to_slice a)
  let o ← x.from_le_bytes s
  let r ← core.option.Option.ok_or o verifier.Error.Checkpoint
  ok (r, self1)

/-- [aspis_r1_cost_probe::verifier::read_checkpoint_weights]: loop body 0:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 364:4-371:1 -/
@[rust_loop_body]
def verifier.read_checkpoint_weights_loop.body (x : Ext)
  (bytes : Slice Std.U8) (iter : core.slice.iter.IterMut aspis_core.field.QM31)
  (back : core.slice.iter.IterMut aspis_core.field.QM31 →
  core.slice.iter.IterMut aspis_core.field.QM31) (at1 : Std.Usize) :
  Result (ControlFlow ((core.slice.iter.IterMut aspis_core.field.QM31) ×
    (core.slice.iter.IterMut aspis_core.field.QM31 → core.slice.iter.IterMut
    aspis_core.field.QM31) × Std.Usize) (Std.Usize × (Option
    (core.result.Result ((alloc.vec.Vec aspis_core.field.QM31) × Std.Usize)
    verifier.Error)) × (core.slice.iter.IterMut aspis_core.field.QM31)))
  := do
  let (o, iter1, next_back) ← core.slice.iter.IteratorIterMut.next iter
  match o with
  | none => let im := next_back iter1 none
            ok (done (at1, none, back im))
  | some _ =>
    let (r, reader) ← verifier.Reader.k x { bytes, «at» := at1 }
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      ok (cont (iter1, fun im => let im1 := next_back im (some val)
                                 back im1, reader.«at»))
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          ((alloc.vec.Vec aspis_core.field.QM31) × Std.Usize)
          (core.convert.FromSame verifier.Error) residual
      let im := next_back iter1 o
      ok (done (at1, some r1, back im))

/-- [aspis_r1_cost_probe::verifier::read_checkpoint_weights]: loop 0:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 364:4-371:1 -/
@[rust_loop]
def verifier.read_checkpoint_weights_loop (x : Ext)
  (iter : core.slice.iter.IterMut aspis_core.field.QM31)
  (back : core.slice.iter.IterMut aspis_core.field.QM31 →
  core.slice.iter.IterMut aspis_core.field.QM31) (bytes : Slice Std.U8)
  (at1 : Std.Usize) :
  Result (Std.Usize × (Option (core.result.Result ((alloc.vec.Vec
    aspis_core.field.QM31) × Std.Usize) verifier.Error)) ×
    (core.slice.iter.IterMut aspis_core.field.QM31))
  := do
  loop
    (fun (iter1, back1, at2) => verifier.read_checkpoint_weights_loop.body x
      bytes iter1 back1 at2)
    (iter, back, at1)

/-- [aspis_r1_cost_probe::verifier::read_checkpoint_weights]:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 363:0-371:1 -/
def verifier.read_checkpoint_weights (x : Ext)
  (bytes : Slice Std.U8) (at1 : Std.Usize)
  (weights : alloc.vec.Vec aspis_core.field.QM31) :
  Result (core.result.Result ((alloc.vec.Vec aspis_core.field.QM31) ×
    Std.Usize) verifier.Error)
  := do
  let (iter, into_iter_back) ← x.into_iter weights
  let (at2, pending_return, back) ←
    verifier.read_checkpoint_weights_loop x iter (fun im => im) bytes at1
  match pending_return with
  | none =>
    let weights1 := into_iter_back back
    ok (core.result.Result.Ok (weights1, at2))
  | some r => ok r


end PRVFresh_k1
end AspisR1.Port5Q2_ReaderWeights

namespace PRVEq.Port5Q2_k1
open AspisR1.Port5Q2_ReaderWeights

set_option maxHeartbeats 200000
theorem loop_body_eq (x : PRVFresh_k1.Ext) :
    PRVFresh_k1.verifier.read_checkpoint_weights_loop.body x =
    AspisR1.Port5Q2_ReaderWeights.weights_loop.body (PRVFresh_k1.verifier.Reader.k x) := rfl

theorem loop_eq (x : PRVFresh_k1.Ext) :
    PRVFresh_k1.verifier.read_checkpoint_weights_loop x =
    AspisR1.Port5Q2_ReaderWeights.weights_loop (PRVFresh_k1.verifier.Reader.k x) := rfl

/-- The only binding: the emission's Vec-IterMut external is the gate's hand model. -/
theorem weights_eq (x : PRVFresh_k1.Ext) (hInto : x.into_iter = AspisR1.Port5Q2_ReaderWeights.intoIter) :
    PRVFresh_k1.verifier.read_checkpoint_weights x =
    AspisR1.Port5Q2_ReaderWeights.weights (PRVFresh_k1.verifier.Reader.k x) := by
  funext bytes at1 w
  unfold PRVFresh_k1.verifier.read_checkpoint_weights AspisR1.Port5Q2_ReaderWeights.weights
  rw [hInto]
  rfl

theorem binding_satisfiable : ∃ x : PRVFresh_k1.Ext, x.into_iter = AspisR1.Port5Q2_ReaderWeights.intoIter :=
  ⟨{ from_le_bytes := fun _ => .fail .panic, into_iter := AspisR1.Port5Q2_ReaderWeights.intoIter }, rfl⟩

end PRVEq.Port5Q2_k1
set_option maxHeartbeats 200000

#print axioms PRVEq.Port5Q2_k1.loop_body_eq
#print axioms PRVEq.Port5Q2_k1.loop_eq
#print axioms PRVEq.Port5Q2_k1.weights_eq
#print axioms PRVEq.Port5Q2_k1.binding_satisfiable
