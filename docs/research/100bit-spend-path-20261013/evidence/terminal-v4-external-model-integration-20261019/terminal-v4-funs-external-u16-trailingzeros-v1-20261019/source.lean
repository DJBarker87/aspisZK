-- Current generated v4 FunsExternal module with three modelled operations imported.
import Aeneas
import Lean.Elab.Tactic.Omega
import AspisR1SelectedMaskProbe.Types
import TerminalStandardOperationModelsV1
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
open AspisR1SelectedMaskProbe

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


/-- [core::array::{impl core::iter::traits::collect::IntoIterator<&'a mut T, core::slice::iter::IterMut<'a, T>> for &'a mut [T; N]}::into_iter]:
    Source: '/rustc/library/core/src/array/mod.rs', lines 376:4-376:40
    Name pattern: [core::array::{core::iter::traits::collect::IntoIterator<&'a mut [@T; @N], &'a mut @T, core::slice::iter::IterMut<'a, @T>>}::into_iter]
    Visibility: public -/
@[rust_fun
  "core::array::{core::iter::traits::collect::IntoIterator<&'a mut [@T; @N], &'a mut @T, core::slice::iter::IterMut<'a, @T>>}::into_iter"]
axiom MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter
  {T : Type} {N : Std.Usize} :
  Array T N → Result ((core.slice.iter.IterMut T) × (core.slice.iter.IterMut
    T → Array T N))


/-- [core::iter::adapters::rev::{impl core::iter::traits::iterator::Iterator<Clause0_Clause0_Item> for core::iter::adapters::rev::Rev<I>}::fold]:
    Source: '/rustc/library/core/src/iter/adapters/rev.rs', lines 79:4-81:41
    Name pattern: [core::iter::adapters::rev::{core::iter::traits::iterator::Iterator<core::iter::adapters::rev::Rev<@I>, @Clause0_Clause0_Item>}::fold]
    Visibility: public -/
@[rust_fun
  "core::iter::adapters::rev::{core::iter::traits::iterator::Iterator<core::iter::adapters::rev::Rev<@I>, @Clause0_Clause0_Item>}::fold"]
axiom core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.fold
  {I : Type} {Acc : Type} {F : Type} {Clause0_Clause0_Item : Type}
  (traitsdouble_endedDoubleEndedIteratorInst :
  core.iter.traits.double_ended.DoubleEndedIterator I Clause0_Clause0_Item)
  (opsfunctionFnMutFPairAccInst : core.ops.function.FnMut F (Acc ×
  Clause0_Clause0_Item) Acc) :
  core.iter.adapters.rev.Rev I → Acc → F → Result Acc


/-- [core::iter::range::{impl core::iter::traits::iterator::Iterator<A> for core::ops::range::RangeInclusive<A>}::fold]:
    Source: '/rustc/library/core/src/iter/mod.rs', lines 374:8-376:47
    Name pattern: [core::iter::range::{core::iter::traits::iterator::Iterator<core::ops::range::RangeInclusive<@A>, @A>}::fold]
    Visibility: public -/
@[rust_fun
  "core::iter::range::{core::iter::traits::iterator::Iterator<core::ops::range::RangeInclusive<@A>, @A>}::fold"]
axiom core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.fold
  {A : Type} {AAA : Type} {FFF : Type} (StepInst : core.iter.range.Step A)
  (opsfunctionFnMutFFFPairAAAInst : core.ops.function.FnMut FFF (AAA × A) AAA)
  :
  core.ops.range.RangeInclusive A → AAA → FFF → Result AAA


/-- [core::iter::traits::iterator::Iterator::fold]:
    Source: '/rustc/library/core/src/iter/traits/iterator.rs', lines 2664:4-2667:64
    Name pattern: [core::iter::traits::iterator::Iterator::fold]
    Visibility: public -/
@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::fold"]
axiom core.iter.traits.iterator.Iterator.fold.default
  {Self : Type} {B : Type} {F : Type} {Clause0_Item : Type} (IteratorInst :
  core.iter.traits.iterator.Iterator Self Clause0_Item)
  (opsfunctionFnMutFPairBInst : core.ops.function.FnMut F (B × Clause0_Item)
  B) :
  Self → B → F → Result B


/-- [core::num::{u16}::count_ones]:
    Source: '/rustc/library/core/src/num/uint_macros.rs', lines 84:8-84:44
    Name pattern: [core::num::{u16}::count_ones]
    Visibility: public -/
def core.num.U16.count_ones_aux (n : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => (if Nat.testBit n k then 1 else 0) + core.num.U16.count_ones_aux n k

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

/-- [core::slice::iter::{impl core::iter::traits::iterator::Iterator<&'a T> for core::slice::iter::Iter<'a, T>}::fold]:
    Source: '/rustc/library/core/src/slice/iter/macros.rs', lines 259:12-261:49
    Name pattern: [core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Iter<'a, @T>, &'a @T>}::fold]
    Visibility: public -/
@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Iter<'a, @T>, &'a @T>}::fold"]
axiom core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.fold
  {T : Type} {B : Type} {F : Type} (opsfunctionFnMutFPairBSharedATBInst :
  core.ops.function.FnMut F (B × T) B) :
  core.slice.iter.Iter T → B → F → Result B


/-- [core::slice::iter::{impl core::iter::traits::double_ended::DoubleEndedIterator<&'_ T> for core::slice::iter::Iter<'a, T>}::next_back]:
    Source: '/rustc/library/core/src/slice/iter/macros.rs', lines 438:12-438:52
    Name pattern: [core::slice::iter::{core::iter::traits::double_ended::DoubleEndedIterator<core::slice::iter::Iter<'a, @T>, &'_ @T>}::next_back]
    Visibility: public -/
@[rust_fun
  "core::slice::iter::{core::iter::traits::double_ended::DoubleEndedIterator<core::slice::iter::Iter<'a, @T>, &'_ @T>}::next_back"]
axiom
  core.slice.iter.Iter.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedT.next_back
  {T : Type} :
  core.slice.iter.Iter T → Result ((Option T) × (core.slice.iter.Iter T))


#print axioms core.num.U16.count_ones_nat_le
#print axioms core.num.U16.count_ones

#print axioms core.num.U16.trailing_zeros_nat_le
#print axioms core.num.U16.trailing_zeros
