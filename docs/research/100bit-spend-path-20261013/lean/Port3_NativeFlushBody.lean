import Port3_NativePendingPrefix
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port3_NativeFlushBody
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2
abbrev Enum := core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut aspis_core.field.QM31)
structure Ops where
  next : Enum → Result (Option (Usize × aspis_core.field.QM31) × Enum ×
    (Enum → Option (Usize × aspis_core.field.QM31) → Enum))
  enumerate : core.slice.iter.IterMut aspis_core.field.QM31 →
    Result (Enum × ((Enum → Enum) → core.slice.iter.IterMut aspis_core.field.QM31))
def verifier.BatchedWeights.finish_loop.body (ops : Ops)
  (value : verifier.BatchedWeights → Usize → Result aspis_core.field.QM31)
  (self : verifier.BatchedWeights)
  (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut
  aspis_core.field.QM31))
  (back : core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut
  aspis_core.field.QM31) → core.iter.adapters.enumerate.Enumerate
  (core.slice.iter.IterMut aspis_core.field.QM31)) :
  Result (ControlFlow ((core.iter.adapters.enumerate.Enumerate
    (core.slice.iter.IterMut aspis_core.field.QM31)) ×
    (core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut
    aspis_core.field.QM31) → core.iter.adapters.enumerate.Enumerate
    (core.slice.iter.IterMut aspis_core.field.QM31)))
    (core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut
    aspis_core.field.QM31) → core.iter.adapters.enumerate.Enumerate
    (core.slice.iter.IterMut aspis_core.field.QM31)))
  := do
  let (o, iter1, next_back) ←
    ops.next iter
  match o with
  | none => ok (done (fun e => let e1 := next_back e none
                               back e1))
  | some p =>
    let (i, _) := p
    let w ← value self i
    ok (cont (iter1, fun e => let e1 := next_back e (some (i, w))
                              back e1))

/-- [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::BatchedWeights}::finish]: loop 0:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 226:38-226:100 -/
@[rust_loop]
def verifier.BatchedWeights.finish_loop (ops : Ops)
  (value : verifier.BatchedWeights → Usize → Result aspis_core.field.QM31)
  (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut
  aspis_core.field.QM31))
  (back : core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut
  aspis_core.field.QM31) → core.iter.adapters.enumerate.Enumerate
  (core.slice.iter.IterMut aspis_core.field.QM31))
  (self : verifier.BatchedWeights) :
  Result (core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut
    aspis_core.field.QM31) → core.iter.adapters.enumerate.Enumerate
    (core.slice.iter.IterMut aspis_core.field.QM31))
  := do
  loop
    (fun (iter1, back1) => verifier.BatchedWeights.finish_loop.body ops value self iter1
      back1)
    (iter, back)

/-- [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::BatchedWeights}::finish]:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 226:4-226:101 -/
def verifier.BatchedWeights.finish (ops : Ops)
  (value : verifier.BatchedWeights → Usize → Result aspis_core.field.QM31)
  (self : verifier.BatchedWeights) (weights : Slice aspis_core.field.QM31) :
  Result (Slice aspis_core.field.QM31)
  := do
  let (im, iter_mut_back) ← core.slice.Slice.iter_mut weights
  let (iter, enumerate_back) ←
    ops.enumerate im
  let back ← verifier.BatchedWeights.finish_loop ops value iter (fun e => e) self
  let im1 := enumerate_back back
  ok (iter_mut_back im1)


#print axioms verifier.BatchedWeights.finish
end AspisR1.Port3_NativeFlushBody
end
