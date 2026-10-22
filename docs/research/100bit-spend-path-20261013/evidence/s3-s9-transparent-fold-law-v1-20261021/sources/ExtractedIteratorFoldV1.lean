import Aeneas
open Aeneas Aeneas.Std Result ControlFlow Error
noncomputable section
namespace AspisR1S9FactoredCut

/-- [core::iter::traits::iterator::Iterator::fold]: loop body 0:
    Source: '/rustc/library/core/src/iter/traits/iterator.rs', lines 2670:8-2672:9
    Name pattern: [core::iter::traits::iterator::Iterator::fold]
    Visibility: public -/
@[rust_loop_body, trait_default, rust_fun
  "core::iter::traits::iterator::Iterator::fold"]
def core.iter.traits.iterator.Iterator.fold.default_loop.body
  {Self : Type} {B : Type} {F : Type} {Clause0_Item : Type} (IteratorInst :
  core.iter.traits.iterator.Iterator Self Clause0_Item)
  (opsfunctionFnMutFPairBInst : core.ops.function.FnMut F (B × Clause0_Item)
  B) (self : Self) (f : F) (accum : B) :
  Result (ControlFlow (Self × F × B) B)
  := do
  let (o, self1) ← IteratorInst.next self
  match o with
  | none => ok (done accum)
  | some x =>
    let (accum1, f1) ← opsfunctionFnMutFPairBInst.call_mut f (accum, x)
    ok (cont (self1, f1, accum1))

/-- [core::iter::traits::iterator::Iterator::fold]: loop 0:
    Source: '/rustc/library/core/src/iter/traits/iterator.rs', lines 2670:8-2672:9
    Name pattern: [core::iter::traits::iterator::Iterator::fold]
    Visibility: public -/
@[rust_loop, trait_default, rust_fun
  "core::iter::traits::iterator::Iterator::fold"]
def core.iter.traits.iterator.Iterator.fold.default_loop
  {Self : Type} {B : Type} {F : Type} {Clause0_Item : Type} (IteratorInst :
  core.iter.traits.iterator.Iterator Self Clause0_Item)
  (opsfunctionFnMutFPairBInst : core.ops.function.FnMut F (B × Clause0_Item)
  B) (self : Self) (f : F) (accum : B) :
  Result B
  := do
  loop
    (fun (self1, f1, accum1) =>
      core.iter.traits.iterator.Iterator.fold.default_loop.body IteratorInst
      opsfunctionFnMutFPairBInst self1 f1 accum1)
    (self, f, accum)

/-- [core::iter::traits::iterator::Iterator::fold]:
    Source: '/rustc/library/core/src/iter/traits/iterator.rs', lines 2664:4-2667:64
    Name pattern: [core::iter::traits::iterator::Iterator::fold]
    Visibility: public -/
@[reducible, trait_default, rust_fun
  "core::iter::traits::iterator::Iterator::fold"]
def core.iter.traits.iterator.Iterator.fold.default
  {Self : Type} {B : Type} {F : Type} {Clause0_Item : Type} (IteratorInst :
  core.iter.traits.iterator.Iterator Self Clause0_Item)
  (opsfunctionFnMutFPairBInst : core.ops.function.FnMut F (B × Clause0_Item)
  B) (self : Self) (init : B) (f : F) :
  Result B
  := do
  core.iter.traits.iterator.Iterator.fold.default_loop IteratorInst
    opsfunctionFnMutFPairBInst self f init

end AspisR1S9FactoredCut
