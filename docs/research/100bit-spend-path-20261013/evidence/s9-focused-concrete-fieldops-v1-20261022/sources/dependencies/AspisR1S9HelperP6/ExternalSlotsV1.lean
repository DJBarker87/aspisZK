import Aeneas
import AspisR1S9HelperP6.Types
import S4FromFnP6GeneratedInterface
import RangeFoldP6ModelV1
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
open AspisR1S9HelperP6

namespace AspisR1S9HelperP6

/-- Typed operation boundary replacing exactly the six fail/panic field stubs
in the diagnostic Aeneas template. The methods are explicit values, never
axioms; their denotational field laws are a separate caller obligation. -/
class FieldOps where
  qmMul : field.QM31 → field.QM31 → Result field.QM31
  qmSquare : field.QM31 → Result field.QM31
  wideAdd : field.WideExact → field.WideExact → Result field.WideExact
  wideMul : field.WideExact → field.WideExact → Result field.WideExact
  wideMulM31 : field.WideExact → field.M31 → Result field.WideExact
  wideMulQM31 : field.WideExact → field.QM31 → Result field.WideExact
  iterFold : ∀ {Self B F Item : Type}
    (IteratorInst : core.iter.traits.iterator.Iterator Self Item)
    (FnMutInst : core.ops.function.FnMut F (B × Item) B),
    Self → B → F → Result B


/-- Concrete P6 model for the array constructor's stateful FnMut callback. -/
@[reducible] def core.array.from_fn {T F : Type} [FieldOps]
    (N : Std.Usize) (callback : core.ops.function.FnMut F Std.Usize T) :
    F → Result (Array T N × (F × Std.Usize)) := fun initial =>
      AspisR1FromFnP6Generated.core.array.from_fn_model N callback initial

/-- Explicit P6 obligation for `Iterator::fold.default`. The generated
source caller supplies the `IteratorRange StepUsize` instance. `iterFoldRange`
models that specialization using the pinned Aeneas `RangeIter.next` and the
accepted range-fold theorem; a concrete instance must satisfy this equation. -/
def iterFoldRange {B F : Type}
    (FnMutInst : core.ops.function.FnMut F (B × Std.Usize) B)
    (range : core.ops.range.Range Std.Usize) (initial : B) (closure : F) : Result B := do
  let step : (B × F) → Std.Usize → Result (B × F) := fun state index => do
    let (value, closure') ← FnMutInst.call_mut state.2 (state.1, index)
    ok (value, closure')
  let (value, _) ← AspisR1S3S9RangeFoldP6.rangeFoldRun
    (range.end.val - range.start.val) range step (initial, closure)
  ok value

@[reducible] def core.iter.traits.iterator.Iterator.fold.default [FieldOps]
    {Self B F Item : Type}
    (IteratorInst : core.iter.traits.iterator.Iterator Self Item)
    (FnMutInst : core.ops.function.FnMut F (B × Item) B) :
    Self → B → F → Result B := FieldOps.iterFold IteratorInst FnMutInst

/-- No axiom: this is the exact interface needed to instantiate the concrete
range fold with the selected P6 operational model. -/
def IteratorFoldRangeP6Law (ops : FieldOps) : Prop :=
  ∀ {B F : Type}
    (FnMutInst : core.ops.function.FnMut F (B × Std.Usize) B)
    (range : core.ops.range.Range Std.Usize) (initial : B) (closure : F),
    ops.iterFold
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
      FnMutInst range initial closure = iterFoldRange FnMutInst range initial closure

end AspisR1S9HelperP6
