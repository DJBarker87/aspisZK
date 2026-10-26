import FIq_NativeTypes
import SelectorArrayMapRuntimeSlice
open Aeneas Aeneas.Std Result ControlFlow Error
namespace FIq_Native
/-- [core::array::iter::{impl core::iter::traits::collect::IntoIterator<T, core::array::iter::IntoIter<T, N>> for [T; N]}::into_iter]:
    Source: '/rustc/library/core/src/array/iter.rs', lines 56:4-56:40
    Name pattern: [core::array::iter::{core::iter::traits::collect::IntoIterator<[@T; @N], @T, core::array::iter::IntoIter<@T, @N>>}::into_iter]
    Visibility: public -/
@[rust_fun
  "core::array::iter::{core::iter::traits::collect::IntoIterator<[@T; @N], @T, core::array::iter::IntoIter<@T, @N>>}::into_iter"]
axiom Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter
  {T : Type} {N : Std.Usize} :
  Array T N → Result (core.array.iter.IntoIter T N)


/-- [core::array::iter::{impl core::iter::traits::iterator::Iterator<T> for core::array::iter::IntoIter<T, N>}::fold]:
    Source: '/rustc/library/core/src/array/iter.rs', lines 252:4-254:44
    Name pattern: [core::array::iter::{core::iter::traits::iterator::Iterator<core::array::iter::IntoIter<@T, @N>, @T>}::fold]
    Visibility: public -/
@[rust_fun
  "core::array::iter::{core::iter::traits::iterator::Iterator<core::array::iter::IntoIter<@T, @N>, @T>}::fold"]
axiom core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.fold
  {T : Type} {Acc : Type} {Fold : Type} {N : Std.Usize}
  (opsfunctionFnMutFoldPairAccInst : core.ops.function.FnMut Fold (Acc × T)
  Acc) :
  core.array.iter.IntoIter T N → Acc → Fold → Result Acc


/-- [core::array::iter::{impl core::iter::traits::iterator::Iterator<T> for core::array::iter::IntoIter<T, N>}::next]:
    Source: '/rustc/library/core/src/array/iter.rs', lines 242:4-242:44
    Name pattern: [core::array::iter::{core::iter::traits::iterator::Iterator<core::array::iter::IntoIter<@T, @N>, @T>}::next]
    Visibility: public -/
@[rust_fun
  "core::array::iter::{core::iter::traits::iterator::Iterator<core::array::iter::IntoIter<@T, @N>, @T>}::next"]
axiom core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next
  {T : Type} {N : Std.Usize} :
  core.array.iter.IntoIter T N → Result ((Option T) ×
    (core.array.iter.IntoIter T N))


/-- [core::array::iter::{impl core::iter::traits::double_ended::DoubleEndedIterator<T> for core::array::iter::IntoIter<T, N>}::next_back]:
    Source: '/rustc/library/core/src/array/iter.rs', lines 297:4-297:49
    Name pattern: [core::array::iter::{core::iter::traits::double_ended::DoubleEndedIterator<core::array::iter::IntoIter<@T, @N>, @T>}::next_back]
    Visibility: public -/
@[rust_fun
  "core::array::iter::{core::iter::traits::double_ended::DoubleEndedIterator<core::array::iter::IntoIter<@T, @N>, @T>}::next_back"]
axiom
  core.array.iter.IntoIter.Insts.CoreIterTraitsDouble_endedDoubleEndedIterator.next_back
  {T : Type} {N : Std.Usize} :
  core.array.iter.IntoIter T N → Result ((Option T) ×
    (core.array.iter.IntoIter T N))


def core.num.U16.count_ones_aux (n : Nat) : Nat → Nat
  | 0 => 0
  | k+1 => (if Nat.testBit n k then 1 else 0) + core.num.U16.count_ones_aux n k

def core.num.U16.count_ones_nat (x : Std.U16) : Nat :=
  core.num.U16.count_ones_aux (UScalar.val x) 16

theorem core.num.U16.count_ones_aux_le (n k : Nat) :
    core.num.U16.count_ones_aux n k ≤ k := by
  induction k with
  | zero => simp [core.num.U16.count_ones_aux]
  | succ k ih =>
      simp only [core.num.U16.count_ones_aux]
      split <;> omega

theorem core.num.U16.count_ones_nat_le (x : Std.U16) :
    core.num.U16.count_ones_nat x ≤ 16 := by
  exact core.num.U16.count_ones_aux_le (UScalar.val x) 16

/-- Candidate model for Rust u16::count_ones using the 16 value bits. -/
@[rust_fun "core::num::{u16}::count_ones"]
def core.num.U16.count_ones (x : Std.U16) : Result Std.U32 :=
  .ok (UScalar.mk (BitVec.ofNat 32 (core.num.U16.count_ones_nat x)))


/-- [core::num::{u16}::trailing_zeros]:
    Source: '/rustc/library/core/src/num/uint_macros.rs', lines 177:8-177:48
    Name pattern: [core::num::{u16}::trailing_zeros]
    Visibility: public -/
def core.num.U16.trailing_zeros_aux (n : Nat) : Nat → Nat
  | 0 => 16
  | k + 1 => if Nat.testBit n k then min k (core.num.U16.trailing_zeros_aux n k)
             else core.num.U16.trailing_zeros_aux n k

def core.num.U16.trailing_zeros_nat (x : Std.U16) : Nat :=
  core.num.U16.trailing_zeros_aux (UScalar.val x) 16

theorem core.num.U16.trailing_zeros_aux_le (n k : Nat) :
    core.num.U16.trailing_zeros_aux n k ≤ 16 := by
  induction k with
  | zero => simp [core.num.U16.trailing_zeros_aux]
  | succ k ih =>
      unfold core.num.U16.trailing_zeros_aux
      split
      · exact le_trans (Nat.min_le_right _ _) ih
      · exact ih

theorem core.num.U16.trailing_zeros_nat_le (x : Std.U16) :
    core.num.U16.trailing_zeros_nat x ≤ 16 := by
  exact core.num.U16.trailing_zeros_aux_le (UScalar.val x) 16

/-- Candidate model for Rust u16::trailing_zeros; zero has width 16. -/
@[rust_fun "core::num::{u16}::trailing_zeros"]
def core.num.U16.trailing_zeros (x : Std.U16) : Result Std.U32 :=
  .ok (UScalar.mk (BitVec.ofNat 32 (core.num.U16.trailing_zeros_nat x)))


/-- Namespace-rebound implementation of derived `Range.clone`, copied from the accepted SumHighStdModels body. -/
def core.ops.range.Range.Insts.CoreCloneClone.clone {Idx : Type}
    (cloneCloneInst : core.clone.Clone Idx)
    (r : core.ops.range.Range Idx) : Result (core.ops.range.Range Idx) := do
  let start ← cloneCloneInst.clone r.start
  let finish ← cloneCloneInst.clone r.end
  .ok { start := start, «end» := finish }

theorem range_clone_usize (r : core.ops.range.Range Usize) :
    core.ops.range.Range.Insts.CoreCloneClone.clone Aeneas.Std.core.clone.CloneUsize r = .ok r := by
  rfl

#print axioms range_clone_usize

/-- Namespace-rebound current Aeneas implementation of Option PartialEq::eq, copied from the selected terminal-validator model. -/
@[rust_fun
  "core::option::{core::cmp::PartialEq<core::option::Option<@T>, core::option::Option<@T>>}::eq"]
def core.option.Option.Insts.CoreCmpPartialEqOption.eq
  {T : Type} (cmpPartialEqInst : core.cmp.PartialEq T T) (self : Option T)
  (other : Option T) :
  Result Bool
  := do
  match self with
  | none =>
      match other with
      | none => ok true
      | some _ => ok false
  | some l =>
      match other with
      | none => ok false
      | some r => cmpPartialEqInst.eq l r

#print axioms core.option.Option.Insts.CoreCmpPartialEqOption.eq


def core.result.Result.map
    {T E U F : Type}
    (callback : core.ops.function.FnOnce F T U)
    (self : core.result.Result T E) (op : F) : Result (core.result.Result U E) := do
  match self with
  | .Ok value =>
      let mapped ← callback.call_once op value
      .ok (.Ok mapped)
  | .Err error => .ok (.Err error)

def core.result.Result.map_err
    {T E F O : Type}
    (callback : core.ops.function.FnOnce O E F)
    (self : core.result.Result T E) (op : O) : Result (core.result.Result T F) := do
  match self with
  | .Ok value => .ok (.Ok value)
  | .Err error =>
      let mapped ← callback.call_once op error
      .ok (.Err mapped)

def core.array.Array.map
    {T F U : Type} {N : Usize}
    (callback : core.ops.function.FnMut F T U)
    (self : Array T N) (f : F) : Result (Array U N) :=
  Aeneas.Std.core.array.Array.map callback self f

#print axioms core.result.Result.map
#print axioms core.result.Result.map_err
#print axioms core.array.Array.map



def MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter
    {T : Type} {N : Usize} (a : Array T N) :
    Result (core.slice.iter.IterMut T × (core.slice.iter.IterMut T → Array T N)) :=
  ok (⟨a.to_slice,0⟩,fun it =>
    ⟨a.val.mapIdx (fun i old => it.slice.val[i]?.getD old),by simpa only [List.length_mapIdx] using a.property⟩)

def revFold {I Acc F Item : Type}
    (it : core.iter.traits.double_ended.DoubleEndedIterator I Item)
    (fn : core.ops.function.FnMut F (Acc × Item) Acc)
    (self : I) (acc : Acc) (f : F) : Result Acc := do
  let (item,rest) ← it.next_back self
  match item with
  | none => ok acc
  | some x =>
    let (next,f') ← fn.call_mut f (acc,x)
    revFold it fn rest next f'
partial_fixpoint

def core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.fold
    {I Acc F Item : Type}
    (it : core.iter.traits.double_ended.DoubleEndedIterator I Item)
    (fn : core.ops.function.FnMut F (Acc × Item) Acc)
    (self : core.iter.adapters.rev.Rev I) (acc : Acc) (f : F) : Result Acc :=
  revFold it fn self.iter acc f

def rangeFold {A Acc F : Type} (step : core.iter.range.Step A)
    (fn : core.ops.function.FnMut F (Acc × A) Acc)
    (self : core.ops.range.RangeInclusive A) (acc : Acc) (f : F) : Result Acc := do
  let (item,rest) ← Aeneas.Std.core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next step self
  match item with
  | none => ok acc
  | some x =>
    let (next,f') ← fn.call_mut f (acc,x)
    rangeFold step fn rest next f'
partial_fixpoint

def core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.fold := @rangeFold

def core.slice.iter.Iter.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedT.next_back
    {T : Type} (it : core.slice.iter.Iter T) : Result (Option T × core.slice.iter.Iter T) :=
  if it.i < it.slice.val.length then
    ok (it.slice.val.getLast?, {it with slice:=⟨it.slice.val.dropLast,by
      have h := it.slice.property
      exact Nat.le_trans (by simp) h⟩})
  else ok (none,it)

end FIq_Native
