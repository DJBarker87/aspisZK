import R1Z.ProverRwP7CoefficientTable
import R1Z.ProverRwP7ShiftCount
import R1Z.ProverRwP7BodyFibre
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_ProverRwP7CoefficientsSource
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
abbrev core.array.from_fn := @ProverRwSuccessArrayFromFn.fromFn
abbrev aspis_core.r0.transport.order := ProverRwP7CoefficientTable.table.coefficient_table
abbrev transport.Variant := ProverRwFull.transport.Variant
abbrev transport.Variant.coefficients.closure (T : Type) := Array T 1024#usize × transport.Variant
/-- [aspis_core::r0::transport::COEFFICIENT_TO_ROW]
    Source: 'crates/aspis-core/src/r0/transport.rs', lines 21:0-21:48
    Name pattern: [aspis_core::r0::transport::COEFFICIENT_TO_ROW]
    Visibility: public -/
@[global_simps, irreducible, rust_const
  "aspis_core::r0::transport::COEFFICIENT_TO_ROW"]
def aspis_core.r0.transport.COEFFICIENT_TO_ROW
  : Result (Array Std.U16 1024#usize) :=
  aspis_core.r0.transport.order

/-- [aspis_r1_cost_probe::transport::{impl core::cmp::PartialEq<aspis_r1_cost_probe::transport::Variant> for aspis_r1_cost_probe::transport::Variant}::eq]:
    Source: 'crates/aspis-r1-cost-probe/src/transport.rs', lines 2:26-2:35
    Visibility: public -/
def transport.Variant.Insts.CoreCmpPartialEqVariant.eq
  (self : transport.Variant) (other : transport.Variant) : Result Bool := do
  let self1 := read_discriminant self
  let other1 := read_discriminant other
  ok (self1 = other1)

/-- [aspis_r1_cost_probe::transport::TAU]
    Source: 'crates/aspis-r1-cost-probe/src/transport.rs', lines 4:0-4:44
    Visibility: public -/
@[global_simps, irreducible]
def transport.TAU : Array Std.Usize 5#usize :=
  Array.make 5#usize [ 3#usize, 4#usize, 2#usize, 0#usize, 1#usize ]

/-- [aspis_r1_cost_probe::transport::{aspis_r1_cost_probe::transport::Variant}::row]: loop body 0:
    Source: 'crates/aspis-r1-cost-probe/src/transport.rs', lines 13:8-13:62
    Visibility: public -/
@[rust_loop_body]
def transport.Variant.row_loop.body
  (j : Std.Usize) (iter : core.ops.range.Range Std.Usize) (out : Std.Usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × Std.Usize)
    Std.Usize)
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done out)
  | some d =>
    let i ← lift (Std.Usize.wrapping_mul 2#usize d)
    let i1 ← lift (Std.Usize.wrapping_shr j (UScalar.cast .U32 i))
    let i2 ← lift (i1 &&& 3#usize)
    let i3 ← Array.index_usize transport.TAU d
    let i4 ← lift (Std.Usize.wrapping_mul 2#usize i3)
    let i5 ← lift (Std.Usize.wrapping_shl i2 (UScalar.cast .U32 i4))
    let out1 ← lift (out ||| i5)
    ok (cont (iter1, out1))

/-- [aspis_r1_cost_probe::transport::{aspis_r1_cost_probe::transport::Variant}::row]: loop 0:
    Source: 'crates/aspis-r1-cost-probe/src/transport.rs', lines 13:8-13:62
    Visibility: public -/
@[rust_loop]
def transport.Variant.row_loop
  (iter : core.ops.range.Range Std.Usize) (j : Std.Usize) (out : Std.Usize) :
  Result Std.Usize
  := do
  loop
    (fun (iter1, out1) => transport.Variant.row_loop.body j iter1 out1)
    (iter, out)

/-- [aspis_r1_cost_probe::transport::{aspis_r1_cost_probe::transport::Variant}::row]:
    Source: 'crates/aspis-r1-cost-probe/src/transport.rs', lines 10:4-15:5
    Visibility: public -/
def transport.Variant.row
  (self : transport.Variant) (j : Std.Usize) : Result Std.Usize := do
  let b ←
    transport.Variant.Insts.CoreCmpPartialEqVariant.eq self transport.Variant.D
  if b
  then
    let a ← aspis_core.r0.transport.COEFFICIENT_TO_ROW
    let i ← Array.index_usize a j
    ok (UScalar.cast .Usize i)
  else
    transport.Variant.row_loop { start := 0#usize, «end» := 5#usize } j
      0#usize

/-- [aspis_r1_cost_probe::transport::{aspis_r1_cost_probe::transport::Variant}::coefficients::{impl core::ops::function::FnMut<(usize,), T> for aspis_r1_cost_probe::transport::{aspis_r1_cost_probe::transport::Variant}::coefficients::closure<'_0, '_1, T>}::call_mut]:
    Source: 'crates/aspis-r1-cost-probe/src/transport.rs', lines 17:29-17:49 -/
def
  transport.Variant.coefficients.closure.Insts.CoreOpsFunctionFnMutTupleUsizeT.call_mut
  {T : Type} (coremarkerCopyInst : core.marker.Copy T)
  (c : transport.Variant.coefficients.closure T) (tupled_args : Std.Usize) :
  Result (T × (transport.Variant.coefficients.closure T))
  := do
  let (a, v) := c
  let i ← transport.Variant.row v tupled_args
  let t ← Array.index_usize a i
  ok (t, c)

/-- [aspis_r1_cost_probe::transport::{aspis_r1_cost_probe::transport::Variant}::coefficients::{impl core::ops::function::FnOnce<(usize,), T> for aspis_r1_cost_probe::transport::{aspis_r1_cost_probe::transport::Variant}::coefficients::closure<'_0, '_1, T>}::call_once]:
    Source: 'crates/aspis-r1-cost-probe/src/transport.rs', lines 17:29-17:49 -/
def
  transport.Variant.coefficients.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeT.call_once
  {T : Type} (coremarkerCopyInst : core.marker.Copy T)
  (c : transport.Variant.coefficients.closure T) (i : Std.Usize) :
  Result T
  := do
  let (t, _) ←
    transport.Variant.coefficients.closure.Insts.CoreOpsFunctionFnMutTupleUsizeT.call_mut
      coremarkerCopyInst c i
  ok t

/-- Trait implementation: [aspis_r1_cost_probe::transport::{aspis_r1_cost_probe::transport::Variant}::coefficients::{impl core::ops::function::FnOnce<(usize,), T> for aspis_r1_cost_probe::transport::{aspis_r1_cost_probe::transport::Variant}::coefficients::closure<'_0, '_1, T>}]
    Source: 'crates/aspis-r1-cost-probe/src/transport.rs', lines 17:29-17:49 -/
@[reducible]
def
  transport.Variant.coefficients.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeT
  {T : Type} (coremarkerCopyInst : core.marker.Copy T) :
  core.ops.function.FnOnce (transport.Variant.coefficients.closure T) Std.Usize
  T := {
  call_once :=
    transport.Variant.coefficients.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeT.call_once
    coremarkerCopyInst
}

/-- Trait implementation: [aspis_r1_cost_probe::transport::{aspis_r1_cost_probe::transport::Variant}::coefficients::{impl core::ops::function::FnMut<(usize,), T> for aspis_r1_cost_probe::transport::{aspis_r1_cost_probe::transport::Variant}::coefficients::closure<'_0, '_1, T>}]
    Source: 'crates/aspis-r1-cost-probe/src/transport.rs', lines 17:29-17:49 -/
@[reducible]
def
  transport.Variant.coefficients.closure.Insts.CoreOpsFunctionFnMutTupleUsizeT
  {T : Type} (coremarkerCopyInst : core.marker.Copy T) :
  core.ops.function.FnMut (transport.Variant.coefficients.closure T) Std.Usize
  T := {
  FnOnceInst :=
    transport.Variant.coefficients.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeT
    coremarkerCopyInst
  call_mut :=
    transport.Variant.coefficients.closure.Insts.CoreOpsFunctionFnMutTupleUsizeT.call_mut
    coremarkerCopyInst
}

/-- [aspis_r1_cost_probe::transport::{aspis_r1_cost_probe::transport::Variant}::coefficients]:
    Source: 'crates/aspis-r1-cost-probe/src/transport.rs', lines 16:4-18:5
    Visibility: public -/
def transport.Variant.coefficients
  {T : Type} (coremarkerCopyInst : core.marker.Copy T)
  (self : transport.Variant) (rows : Array T 1024#usize) :
  Result (Array T 1024#usize)
  := do
  core.array.from_fn 1024#usize
    (transport.Variant.coefficients.closure.Insts.CoreOpsFunctionFnMutTupleUsizeT
    coremarkerCopyInst) (rows, self)

-- Expose the complete generic source equation, for every variant and element
-- carrier; no S2-only simplification or output-equality premise is used.
theorem coefficients_unfold {T : Type} (copy : core.marker.Copy T)
    (v : transport.Variant) (rows : Array T 1024#usize) :
    transport.Variant.coefficients copy v rows =
      core.array.from_fn 1024#usize
        (transport.Variant.coefficients.closure.Insts.CoreOpsFunctionFnMutTupleUsizeT copy)
        (rows,v) := rfl
#print axioms coefficients_unfold
end R1Z.PV_ProverRwP7CoefficientsSource
