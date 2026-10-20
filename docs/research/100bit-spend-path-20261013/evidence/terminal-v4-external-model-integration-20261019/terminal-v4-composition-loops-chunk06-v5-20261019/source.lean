-- Ordered generated declaration chunk for the exact composition folds.
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
/-- Compatibility interface for the Aeneas iterator record in this pinned
source environment; next and next_back are the pinned generated external
models, and the recursive loop bodies below are copied verbatim. -/
def core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator
    (T : Type) (N : Std.Usize) :
    core.iter.traits.iterator.Iterator (core.array.iter.IntoIter T N) T := {
      next := core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next
    }

def core.array.iter.IntoIter.Insts.CoreIterTraitsDouble_endedDoubleEndedIterator
    (T : Type) (N : Std.Usize) :
    core.iter.traits.double_ended.DoubleEndedIterator
      (core.array.iter.IntoIter T N) T := {
    iteratorInst := core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator T N
    next_back := core.array.iter.IntoIter.Insts.CoreIterTraitsDouble_endedDoubleEndedIterator.next_back
  }

/-- [aspis_r1_mask_extraction_probe::field::{impl core::clone::Clone for aspis_r1_mask_extraction_probe::field::QM31}::clone]:
    Source: 'src/field.rs', lines 431:9-431:14
    Visibility: public -/
def field.QM31.Insts.CoreCloneClone.clone
  (self : field.QM31) : Result field.QM31 := do
  ok self

/-- Trait implementation: [aspis_r1_mask_extraction_probe::field::{impl core::clone::Clone for aspis_r1_mask_extraction_probe::field::QM31}]
    Source: 'src/field.rs', lines 431:9-431:14 -/
@[reducible]
def field.QM31.Insts.CoreCloneClone : core.clone.Clone field.QM31 := {
  clone := field.QM31.Insts.CoreCloneClone.clone
}

/-- Trait implementation: [aspis_r1_mask_extraction_probe::field::{impl core::marker::Copy for aspis_r1_mask_extraction_probe::field::QM31}]
    Source: 'src/field.rs', lines 431:16-431:20 -/
@[reducible]
def field.QM31.Insts.CoreMarkerCopy : core.marker.Copy field.QM31 := {
  cloneInst := field.QM31.Insts.CoreCloneClone
}

/-- [aspis_r1_mask_extraction_probe::field::{aspis_r1_mask_extraction_probe::field::PreparedQm31Multiplier}::new::{impl core::ops::function::Fn<(aspis_r1_mask_extraction_probe::field::CM31,), [aspis_r1_mask_extraction_probe::field::M31; 3usize]> for aspis_r1_mask_extraction_probe::field::{aspis_r1_mask_extraction_probe::field::PreparedQm31Multiplier}::new::closure}::call]:
    Source: 'src/field.rs', lines 449:22-449:96 -/
def
  field.PreparedQm31Multiplier.new.closure.Insts.CoreOpsFunctionFnTupleCM31ArrayM313.call
  (c : field.PreparedQm31Multiplier.new.closure) (tupled_args : field.CM31) :
  Result (Array field.M31 3#usize)
  := do
  let m ← field.M31.add tupled_args.a tupled_args.b
  ok (Array.make 3#usize [ tupled_args.a, tupled_args.b, m ])

/-- [aspis_r1_mask_extraction_probe::field::{aspis_r1_mask_extraction_probe::field::PreparedQm31Multiplier}::new]:
    Source: 'src/field.rs', lines 448:4-457:5
    Visibility: public -/
def field.PreparedQm31Multiplier.new
  (value : field.QM31) : Result field.PreparedQm31Multiplier := do
  let a ←
    field.PreparedQm31Multiplier.new.closure.Insts.CoreOpsFunctionFnTupleCM31ArrayM313.call
      () value.c0
  let a1 ←
    field.PreparedQm31Multiplier.new.closure.Insts.CoreOpsFunctionFnTupleCM31ArrayM313.call
      () value.c1
  let c ← field.CM31.add value.c0 value.c1
  let a2 ←
    field.PreparedQm31Multiplier.new.closure.Insts.CoreOpsFunctionFnTupleCM31ArrayM313.call
      () c
  ok { components := (Array.make 3#usize [ a, a1, a2 ]) }

/-- [aspis_r1_mask_extraction_probe::field::{aspis_r1_mask_extraction_probe::field::PreparedQm31Multiplier}::mul::{impl core::ops::function::Fn<([aspis_r1_mask_extraction_probe::field::M31; 3usize], aspis_r1_mask_extraction_probe::field::CM31), aspis_r1_mask_extraction_probe::field::CM31> for aspis_r1_mask_extraction_probe::field::{aspis_r1_mask_extraction_probe::field::PreparedQm31Multiplier}::mul::closure}::call]:
    Source: 'src/field.rs', lines 461:23-469:9 -/
def
  field.PreparedQm31Multiplier.mul.closure.Insts.CoreOpsFunctionFnPairArrayM313CM31CM31.call
  (c : field.PreparedQm31Multiplier.mul.closure)
  (tupled_args : ((Array field.M31 3#usize) × field.CM31)) :
  Result field.CM31
  := do
  let (left, right) := tupled_args
  let m ← Array.index_usize left 0#usize
  let m0 ← field.M31.mul m right.a
  let m1 ← Array.index_usize left 1#usize
  let m11 ← field.M31.mul m1 right.b
  let m2 ← Array.index_usize left 2#usize
  let m3 ← field.M31.add right.a right.b
  let m21 ← field.M31.mul m2 m3
  let m4 ← field.M31.sub m0 m11
  let m5 ← field.M31.sub m21 m0
  let m6 ← field.M31.sub m5 m11
  ok { a := m4, b := m6 }

/-- [aspis_r1_mask_extraction_probe::field::{aspis_r1_mask_extraction_probe::field::PreparedQm31Multiplier}::mul]:
    Source: 'src/field.rs', lines 460:4-477:5
    Visibility: public -/
def field.PreparedQm31Multiplier.mul
  (self : field.PreparedQm31Multiplier) (rhs : field.QM31) :
  Result field.QM31
  := do
  let a ← Array.index_usize self.components 0#usize
  let m0 ←
    field.PreparedQm31Multiplier.mul.closure.Insts.CoreOpsFunctionFnPairArrayM313CM31CM31.call
      () (a, rhs.c0)
  let a1 ← Array.index_usize self.components 1#usize
  let m1 ←
    field.PreparedQm31Multiplier.mul.closure.Insts.CoreOpsFunctionFnPairArrayM313CM31CM31.call
      () (a1, rhs.c1)
  let a2 ← Array.index_usize self.components 2#usize
  let c ← field.CM31.add rhs.c0 rhs.c1
  let m2 ←
    field.PreparedQm31Multiplier.mul.closure.Insts.CoreOpsFunctionFnPairArrayM313CM31CM31.call
      () (a2, c)
  let c1 ← field.mul_by_r m1
  let c2 ← field.CM31.add m0 c1
  let c3 ← field.CM31.sub m2 m0
  let c4 ← field.CM31.sub c3 m1
  ok { c0 := c2, c1 := c4 }

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
