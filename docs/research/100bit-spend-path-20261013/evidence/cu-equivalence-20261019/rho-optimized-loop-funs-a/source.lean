import AspisR1RhoOptimizedLoop.FunsExternal
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.unusedVariables false
noncomputable section
namespace AspisR1RhoCoefficients
/-- [aspis_r1_cu_gamma::rho_new::coefficients]: loop body 0:
    Source: 'lib.rs', lines 1009:4-1016:5
    Visibility: public -/
@[rust_loop_body]
def rho_new.coefficients_loop.body
  (power : aspis_core.field.QM31) (next : Std.Usize)
  (basis : Array aspis_core.field.M31 256#usize)
  (iter : core.ops.range.Range Std.Usize)
  (back : Option BatchedWeights → Option BatchedWeights)
  (rows : alloc.vec.Vec aspis_core.field.QM31)
  (pending : Option BatchedWeights) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Option
    BatchedWeights → Option BatchedWeights) × (alloc.vec.Vec
    aspis_core.field.QM31) × (Option BatchedWeights)) ((alloc.vec.Vec
    aspis_core.field.QM31) × (Option BatchedWeights) × (Option BatchedWeights
    → Option BatchedWeights)))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done (rows, pending, back))
  | some j =>
    let (o1, as_deref_mut_back, as_deref_mut_back1) ←
      AspisR1RhoSourceOption.source_reborrow pending
    match o1 with
    | none =>
      let q ←
        alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
          aspis_core.field.QM31) rows j
      let pending1 := as_deref_mut_back none
      let m ← Array.index_usize basis j
      let q1 ← QM31.mul_m31 power m
      let q2 ← aspis_core.field.QM31.add q q1
      let (_, index_mut_back) ←
        alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice
          aspis_core.field.QM31) rows j
      let rows1 := index_mut_back q2
      let i := alloc.vec.Vec.len rows1
      let i1 ← next * i
      let i2 ← i1 + j
      let q3 ←
        alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
          aspis_core.field.QM31) rows1 j
      let we ← aspis_core.field.WideExact.from_qm31 q3
      trace.value 12#u16 i2 we
      let i3 := alloc.vec.Vec.len rows1
      let i4 ← next * i3
      let i5 ← i4 + j
      let we1 ← aspis_core.field.WideExact.from_m31 m
      trace.value 13#u16 i5 we1
      ok (cont (iter1, fun o2 => let o3 := as_deref_mut_back1 o2
                                 back o3, rows1, pending1))
    | some weights =>
      let m ← Array.index_usize basis j
      let weights1 ← BatchedWeights.push weights j power m
      let pending1 := as_deref_mut_back (some weights1)
      let i := alloc.vec.Vec.len rows
      let i1 ← next * i
      let i2 ← i1 + j
      let q ←
        alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
          aspis_core.field.QM31) rows j
      let we ← aspis_core.field.WideExact.from_qm31 q
      trace.value 12#u16 i2 we
      let i3 := alloc.vec.Vec.len rows
      let i4 ← next * i3
      let i5 ← i4 + j
      let we1 ← aspis_core.field.WideExact.from_m31 m
      trace.value 13#u16 i5 we1
      ok (cont (iter1, fun o2 => let o3 := as_deref_mut_back1 o2
                                 back o3, rows, pending1))

/-- [aspis_r1_cu_gamma::rho_new::coefficients]: loop 0:
    Source: 'lib.rs', lines 1009:4-1016:5
    Visibility: public -/
@[rust_loop]
def rho_new.coefficients_loop
  (iter : core.ops.range.Range Std.Usize)
  (back : Option BatchedWeights → Option BatchedWeights)
  (rows : alloc.vec.Vec aspis_core.field.QM31) (power : aspis_core.field.QM31)
  (next : Std.Usize) (basis : Array aspis_core.field.M31 256#usize)
  (pending : Option BatchedWeights) :
  Result ((alloc.vec.Vec aspis_core.field.QM31) × (Option BatchedWeights) ×
    (Option BatchedWeights → Option BatchedWeights))
  := do
  loop
    (fun (iter1, back1, rows1, pending1) => rho_new.coefficients_loop.body
      power next basis iter1 back1 rows1 pending1)
    (iter, back, rows, pending)

/-- [aspis_r1_cu_gamma::rho_new::coefficients]:
    Source: 'lib.rs', lines 1008:0-1018:1
    Visibility: public -/
def rho_new.coefficients
  (rows : alloc.vec.Vec aspis_core.field.QM31) (power : aspis_core.field.QM31)
  (next : Std.Usize) (basis : Array aspis_core.field.M31 256#usize)
  (pending : Option BatchedWeights) :
  Result ((alloc.vec.Vec aspis_core.field.QM31) × (Option BatchedWeights))
  := do
  let i := alloc.vec.Vec.len rows
  let (rows1, pending1, back) ←
    rho_new.coefficients_loop { start := 0#usize, «end» := i } (fun o => o)
      rows power next basis pending
  match pending1 with
  | none => let pending2 := back none
            ok (rows1, pending2)
  | some weights =>
    let i1 ← weights.terms + 1#usize
    let pending2 := back (some { weights with terms := i1 })
    ok (rows1, pending2)


end AspisR1RhoCoefficients
