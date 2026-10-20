-- Exact generated loop declarations for the terminal composition folds.
import Aeneas
import AspisR1SelectedMaskProbe.Types
import AspisR1SelectedMaskProbe.FunsExternal
import TerminalV4EvalSelectorsChunk05FactoredV1
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section
namespace AspisR1SelectedMaskProbe

namespace AspisR1SelectedMaskProbe

/-- Trait implementation: [core::array::iter::{impl core::iter::traits::iterator::Iterator<T> for core::array::iter::IntoIter<T, N>}]
    Source: '/rustc/library/core/src/array/iter.rs', lines 238:0-238:51
    Name pattern: [core::iter::traits::iterator::Iterator<core::array::iter::IntoIter<@T, @N>, @T>] -/
@[reducible, rust_trait_impl
  "core::iter::traits::iterator::Iterator<core::array::iter::IntoIter<@T, @N>, @T>"]
impl_def core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator (T :
  Type) (N : Std.Usize) : core.iter.traits.iterator.Iterator
  (core.array.iter.IntoIter T N) T := {
  next := core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next
  step_by := core.iter.traits.iterator.Iterator.step_by.trait_default
    (core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator T N)
  fold := fun {B : Type} {F : Type} (opsfunctionFnMutPPairPInst :
    core.ops.function.FnMut F (B × T) B) =>
    core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.fold
    opsfunctionFnMutPPairPInst
  rev := fun {Clause0_Clause0_Item : Type}
    (double_endedDoubleEndedIteratorIntoIterPInst :
    core.iter.traits.double_ended.DoubleEndedIterator (core.array.iter.IntoIter
    T N) Clause0_Clause0_Item) =>
    core.iter.traits.iterator.Iterator.rev.trait_default
    (core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator T N)
    double_endedDoubleEndedIteratorIntoIterPInst
}

/-- Trait implementation: [core::array::iter::{impl core::iter::traits::double_ended::DoubleEndedIterator<T> for core::array::iter::IntoIter<T, N>}]
    Source: '/rustc/library/core/src/array/iter.rs', lines 295:0-295:62
    Name pattern: [core::iter::traits::double_ended::DoubleEndedIterator<core::array::iter::IntoIter<@T, @N>, @T>] -/
@[reducible, rust_trait_impl
  "core::iter::traits::double_ended::DoubleEndedIterator<core::array::iter::IntoIter<@T, @N>, @T>"]
def
  core.array.iter.IntoIter.Insts.CoreIterTraitsDouble_endedDoubleEndedIterator
  (T : Type) (N : Std.Usize) :
  core.iter.traits.double_ended.DoubleEndedIterator (core.array.iter.IntoIter T
  N) T := {
  iteratorInst := core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator
    T N
  next_back :=
    core.array.iter.IntoIter.Insts.CoreIterTraitsDouble_endedDoubleEndedIterator.next_back
}

/-- Trait implementation: [core::option::{impl core::cmp::PartialEq<core::option::Option<T>> for core::option::Option<T>}]

@[rust_loop]
def pool_v1.pair_forest_semantic_terminal.composition_parts_loop0
  (iter : core.iter.adapters.rev.Rev (core.array.iter.IntoIter field.QM31
  24#usize)) (prepared_theta : field.PreparedQm31Multiplier)
  (composition : field.QM31) :
  Result field.QM31
  := do
  let (o, iter1) ←
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
      (core.array.iter.IntoIter.Insts.CoreIterTraitsDouble_endedDoubleEndedIterator
      field.QM31 24#usize) iter
  match o with
  | none => ok composition
  | some lane =>
    let q ← field.PreparedQm31Multiplier.mul prepared_theta composition
    let composition1 ← field.QM31.add q lane
    pool_v1.pair_forest_semantic_terminal.composition_parts_loop0 iter1
      prepared_theta composition1
partial_fixpoint

@[rust_loop]
def pool_v1.pair_forest_semantic_terminal.composition_parts_loop1
  (iter : core.iter.adapters.rev.Rev (core.array.iter.IntoIter field.QM31
  4#usize)) (prepared_theta : field.PreparedQm31Multiplier)
  (composition : field.QM31) :
  Result field.QM31
  := do
  let (o, iter1) ←
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
      (core.array.iter.IntoIter.Insts.CoreIterTraitsDouble_endedDoubleEndedIterator
      field.QM31 4#usize) iter
  match o with
  | none => ok composition
  | some lane =>
    let q ← field.PreparedQm31Multiplier.mul prepared_theta composition
    let composition1 ← field.QM31.add q lane
    pool_v1.pair_forest_semantic_terminal.composition_parts_loop1 iter1
      prepared_theta composition1
partial_fixpoint

end AspisR1SelectedMaskProbe
