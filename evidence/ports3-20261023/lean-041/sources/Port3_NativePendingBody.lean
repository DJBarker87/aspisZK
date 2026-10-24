import Port3_Wrapping
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port3_NativePendingBody
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2
abbrev Row := Array U64 4#usize

def allocationError {AllocError : Type} : core.ops.function.FnOnce Unit AllocError verifier.Error :=
  ⟨fun _ _ => ok .Allocation⟩

def body
  (weights : Slice aspis_core.field.QM31)
  (raw1 : alloc.vec.Vec (Array Std.U64 4#usize)) (index : Std.Usize) :
  Result (ControlFlow ((alloc.vec.Vec (Array Std.U64 4#usize)) × Std.Usize)
    (alloc.vec.Vec (Array Std.U64 4#usize)))
  := do
  let i := Slice.len weights
  if index < i
  then
    let w ← Slice.index_usize weights index
    let i1 := w.c0.a
    let i2 ← lift (UScalar.cast .U64 i1)
    let i3 := w.c0.b
    let i4 ← lift (UScalar.cast .U64 i3)
    let i5 := w.c1.a
    let i6 ← lift (UScalar.cast .U64 i5)
    let i7 := w.c1.b
    let i8 ← lift (UScalar.cast .U64 i7)
    let (_, index_mut_back) ←
      alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice (Array
        Std.U64 4#usize)) raw1 index
    let raw2 := index_mut_back (Array.make 4#usize [ i2, i4, i6, i8 ])
    let index1 ← lift (Std.Usize.wrapping_add index 1#usize)
    ok (cont (raw2, index1))
  else ok (done raw1)

/-- [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::BatchedWeights}::new]: loop 0:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 209:8-213:9 -/
@[rust_loop]
def run
  (weights : Slice aspis_core.field.QM31)
  (raw1 : alloc.vec.Vec (Array Std.U64 4#usize)) (index : Std.Usize) :
  Result (alloc.vec.Vec (Array Std.U64 4#usize))
  := do
  loop
    (fun (raw2, index1) => body weights raw2
      index1)
    (raw1, index)

/-- [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::BatchedWeights}::new]:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 206:4-215:5 -/
def extracted {AllocError : Type}
  (filled : Usize → Row → Result (core.result.Result (alloc.vec.Vec Row) AllocError))
  (weights : Slice aspis_core.field.QM31) :
  Result (core.result.Result verifier.BatchedWeights verifier.Error)
  := do
  let i := Slice.len weights
  let a := Array.repeat 4#usize 0#u64
  let r ←
    filled i a
  let r1 ←
    Port3_Constructor.core.result.Result.map_err
      allocationError
      r ()
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let raw1 ← run weights val 0#usize
    ok (core.result.Result.Ok { «raw» := raw1, terms := 0#usize })
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      verifier.BatchedWeights (core.convert.FromSame verifier.Error) residual
end AspisR1.Port3_NativePendingBody
end
