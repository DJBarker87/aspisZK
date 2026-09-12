import Aeneas
import V7WeightAtStandalone.Types

/-!
Executable models for the two standard-library operations left external by the
focused `WeightAccumulator::weight_at` extraction.  These are library models,
not assumptions about Aspis or its cryptography.
-/

open Aeneas Aeneas.Std Result ControlFlow Error
open V7WeightAtStandalone

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxRecDepth 2048

@[rust_fun "core::option::{core::option::Option<@T>}::as_ref"]
def core.option.Option.as_ref {T : Type} (value : Option T) :
    Result (Option T) :=
  .ok value

@[rust_fun
  "alloc::vec::{core::iter::traits::collect::IntoIterator<&'a alloc::vec::Vec<@T>, &'a @T, core::slice::iter::Iter<'a, @T>>}::into_iter"]
def SharedAVec.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter
    {T : Type} (_allocator : Type) (value : alloc.vec.Vec T) :
    Result (core.slice.iter.Iter T) :=
  .ok { slice := ⟨value.val, value.property⟩, i := 0 }
