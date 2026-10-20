import Aeneas
import AspisR1Post25SamplerStd.Types
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
namespace AspisR1Post25Sampler

/-- Caller-supplied interpretations of the standard-library operations that
Aeneas leaves external in the selected sampler cut. No template axioms are
imported; any concrete instance must provide these operations explicitly. -/
class StdOperationModel where
  array_from_fn : {T : Type} → {F : Type} → (N : Std.Usize) →
    core.ops.function.FnMut F Std.Usize T → F → Result (Array T N)
  into_iter_mut : {T : Type} → {N : Std.Usize} →
    Array T N → Result ((core.slice.iter.IterMut T) ×
      (core.slice.iter.IterMut T → Array T N))
  iterator_all_default : {Self : Type} → {F : Type} → {Item : Type} →
    core.iter.traits.iterator.Iterator Self Item →
    core.ops.function.FnMut F Item Bool → Self → F → Result (Bool × Self)
  iter_mut_all : {T : Type} → {F : Type} →
    core.ops.function.FnMut F T Bool →
    core.slice.iter.IterMut T → F → Result (Bool ×
      (core.slice.iter.IterMut T) ×
      (core.slice.iter.IterMut T → core.slice.iter.IterMut T))
  iter_all : {T : Type} → {F : Type} →
    core.ops.function.FnMut F T Bool → core.slice.iter.Iter T → F →
    Result (Bool × core.slice.iter.Iter T)
  iter_mut_next_back : {T : Type} →
    core.slice.iter.IterMut T → Result ((Option T) ×
      (core.slice.iter.IterMut T) ×
      (core.slice.iter.IterMut T → Option T → core.slice.iter.IterMut T))

variable [StdOperationModel]

@[reducible] def core.array.from_fn
    {T : Type} {F : Type} (N : Std.Usize)
    (inst : core.ops.function.FnMut F Std.Usize T) : F → Result (Array T N) :=
  StdOperationModel.array_from_fn N inst

@[reducible] def MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter
    {T : Type} {N : Std.Usize} (xs : Array T N) :
    Result ((core.slice.iter.IterMut T) ×
      (core.slice.iter.IterMut T → Array T N)) :=
  StdOperationModel.into_iter_mut xs

@[reducible] def core.iter.traits.iterator.Iterator.all.default
    {Self : Type} {F : Type} {Item : Type}
    (inst : core.iter.traits.iterator.Iterator Self Item)
    (f : core.ops.function.FnMut F Item Bool) :
    Self → F → Result (Bool × Self) :=
  StdOperationModel.iterator_all_default inst f

@[reducible] def core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT.all
    {T : Type} {F : Type}
    (f : core.ops.function.FnMut F T Bool) :
    core.slice.iter.IterMut T → F → Result (Bool ×
      (core.slice.iter.IterMut T) ×
      (core.slice.iter.IterMut T → core.slice.iter.IterMut T)) :=
  StdOperationModel.iter_mut_all f

@[reducible] def core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.all
    {T : Type} {F : Type}
    (f : core.ops.function.FnMut F T Bool) :
    core.slice.iter.Iter T → F → Result (Bool × core.slice.iter.Iter T) :=
  StdOperationModel.iter_all f

@[reducible] def core.slice.iter.IterMut.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorMutT.next_back
    {T : Type} (it : core.slice.iter.IterMut T) :
    Result ((Option T) × core.slice.iter.IterMut T) := do
  let (value, iter, _) ← StdOperationModel.iter_mut_next_back it
  ok (value, iter)

end AspisR1Post25Sampler
