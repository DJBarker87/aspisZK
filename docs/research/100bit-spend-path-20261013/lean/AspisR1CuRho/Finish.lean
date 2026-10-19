-- Exact declaration slices from the full Aeneas emission; bodies unchanged.
import AspisR1CuRho.Funs
import AspisR1CuRho.MutableIteratorRuntime
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section
namespace AspisR1CuRho
/-- Trait implementation: [core::slice::iter::{impl core::iter::traits::iterator::Iterator<&'a mut T> for core::slice::iter::IterMut<'a, T>}]
    Source: '/rustc/library/core/src/slice/iter/macros.rs', lines 153:8-153:45
    Name pattern: [core::iter::traits::iterator::Iterator<core::slice::iter::IterMut<'a, @T>, &'a mut @T>] -/
@[reducible, rust_trait_impl
  "core::iter::traits::iterator::Iterator<core::slice::iter::IterMut<'a, @T>, &'a mut @T>"]
impl_def core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT (T :
  Type) : core.iter.traits.iterator.Iterator (core.slice.iter.IterMut T) T := {
  next := core.slice.iter.IteratorIterMut.next
  enumerate := core.iter.traits.iterator.Iterator.enumerate.trait_default
    (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT T)
}


/-- [aspis_r1_cu_rho::verifier::{aspis_r1_cu_rho::verifier::BatchedWeights}::finish]: loop body 0:
    Source: 'lib.rs', lines 75:38-75:100 -/
@[rust_loop_body]
def verifier.BatchedWeights.finish_loop.body
  (self : verifier.BatchedWeights)
  (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut
  field.QM31))
  (back : core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut
  field.QM31) → core.iter.adapters.enumerate.Enumerate
  (core.slice.iter.IterMut field.QM31)) :
  Result (ControlFlow ((core.iter.adapters.enumerate.Enumerate
    (core.slice.iter.IterMut field.QM31)) ×
    (core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut
    field.QM31) → core.iter.adapters.enumerate.Enumerate
    (core.slice.iter.IterMut field.QM31)))
    (core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut
    field.QM31)))
  := do
  let (o, iter1, next_back) ←
    core.iter.adapters.enumerate.IteratorEnumerate.next
      (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT
      field.QM31) iter
  match o with
  | none => ok (done (let e := next_back iter1 none
                      back e))
  | some p =>
    let (i, _) := p
    let w ← verifier.BatchedWeights.value self i
    ok (cont (iter1, fun e => let e1 := next_back e (some (i, w))
                              back e1))

/-- [aspis_r1_cu_rho::verifier::{aspis_r1_cu_rho::verifier::BatchedWeights}::finish]: loop 0:
    Source: 'lib.rs', lines 75:38-75:100 -/
@[rust_loop]
def verifier.BatchedWeights.finish_loop
  (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut
  field.QM31))
  (back : core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut
  field.QM31) → core.iter.adapters.enumerate.Enumerate
  (core.slice.iter.IterMut field.QM31)) (self : verifier.BatchedWeights) :
  Result (core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut
    field.QM31))
  := do
  loop
    (fun (iter1, back1) => verifier.BatchedWeights.finish_loop.body self iter1
      back1)
    (iter, back)

/-- [aspis_r1_cu_rho::verifier::{aspis_r1_cu_rho::verifier::BatchedWeights}::finish]:
    Source: 'lib.rs', lines 75:4-75:101 -/
def verifier.BatchedWeights.finish
  (self : verifier.BatchedWeights) (weights : Slice field.QM31) :
  Result (Slice field.QM31)
  := do
  let (im, iter_mut_back) ← core.slice.Slice.iter_mut weights
  let (iter, enumerate_back) ←
    core.iter.traits.iterator.Iterator.enumerate.trait_default
      (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT
      field.QM31) im
  let back ← verifier.BatchedWeights.finish_loop iter (fun e => e) self
  let im1 := enumerate_back back
  ok (iter_mut_back im1)

end AspisR1CuRho
