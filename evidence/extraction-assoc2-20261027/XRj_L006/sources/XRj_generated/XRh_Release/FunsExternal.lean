import Aeneas
import XRh_Release.Types
open Aeneas Aeneas.Std Result ControlFlow Error
open XRh_Release
set_option linter.dupNamespace false

/- Reused definition: aeneas-verif/v7-registry-v2-production-call-composition-20260831/generated/V7PairForestProductionCodecs/FunsExternal.lean:29 -/
def core.iter.traits.iterator.Iterator.any.default
    {Self F Item : Type}
    (iterator : core.iter.traits.iterator.Iterator Self Item)
    (fnMut : core.ops.function.FnMut F Item Bool) :
    Self → F → Result (Bool × Self) :=
  fun self predicate => do
    let outcome ←
      (loop
        (fun (self', predicate') => do
          let (item, self'') ← iterator.next self'
          match item with
          | none => ok (done (false, self'', predicate'))
          | some value =>
              let (accepted, predicate'') ← fnMut.call_mut predicate' value
              if accepted then
                ok (done (true, self'', predicate''))
              else
                ok (cont (self'', predicate'')))
        (self, predicate) : Result (Bool × Self × F))
    ok (outcome.1, outcome.2.1)

/- Reused definition: aeneas-verif/v7-registry-v2-production-call-composition-20260831/generated/V7PairForestProductionCodecs/FunsExternal.lean:51 -/
def core.iter.traits.iterator.Iterator.all.default
    {Self F Item : Type}
    (iterator : core.iter.traits.iterator.Iterator Self Item)
    (fnMut : core.ops.function.FnMut F Item Bool) :
    Self → F → Result (Bool × Self) :=
  fun self predicate => do
    let outcome ←
      (loop
        (fun (self', predicate') => do
          let (item, self'') ← iterator.next self'
          match item with
          | none => ok (done (true, self'', predicate'))
          | some value =>
              let (holds, predicate'') ← fnMut.call_mut predicate' value
              if holds then
                ok (cont (self'', predicate''))
              else
                ok (done (false, self'', predicate'')))
        (self, predicate) : Result (Bool × Self × F))
    ok (outcome.1, outcome.2.1)

/- Reused definition: aeneas-verif/v7-tag73-current-caller-source-20260830/proof/V7Tag73CurrentHelpersOpaque/FunsExternalBase.lean:193 -/
def core.iter.traits.iterator.Iterator.fold.default
    {Self B F Item : Type}
    (iteratorInst : core.iter.traits.iterator.Iterator Self Item)
    (fnMut : core.ops.function.FnMut F (B × Item) B)
    (iterator : Self) (accumulator : B) (closure : F) : Result B := do
  let result : B × Self × F ←
    loop
      (fun (acc, state, closureState) => do
        let (item, stateNext) ← iteratorInst.next state
        match item with
        | none => .ok (.done (acc, stateNext, closureState))
        | some value =>
          let (accNext, closureNext) ←
            fnMut.call_mut closureState (acc, value)
          .ok (.cont (accNext, stateNext, closureNext)))
      (accumulator, iterator, closure)
  .ok result.1

/- Reused definition: aeneas-verif/v7-tag73-current-caller-source-20260830/proof/V7Tag73CurrentHelpersOpaque/FunsExternalBase.lean:220 -/
def core.array.fromFnList
    {T F : Type} (fnMut : core.ops.function.FnMut F Std.Usize T) :
    Nat → Std.Usize → F → Result (List T × F)
  | 0, _, closure => .ok ([], closure)
  | fuel + 1, index, closure => do
      let (value, closureNext) ← fnMut.call_mut closure index
      match fuel with
      | 0 => .ok ([value], closureNext)
      | remaining + 1 =>
        let indexNext ← index + 1#usize
        let (rest, closureFinal) ←
          core.array.fromFnList fnMut (remaining + 1) indexNext closureNext
        .ok (value :: rest, closureFinal)

/- Reused definition: aeneas-verif/v7-tag73-current-caller-source-20260830/proof/V7Tag73CurrentHelpersOpaque/FunsExternalBase.lean:235 -/
def core.array.from_fn
    {T F : Type} (N : Std.Usize)
    (fnMut : core.ops.function.FnMut F Std.Usize T)
    (closure : F) : Result (Array T N) :=
  match core.array.fromFnList fnMut N.val 0#usize closure with
  | .fail error => .fail error
  | .div => .div
  | .ok (values, _) =>
    if h : values.length = N.val then .ok ⟨values, h⟩ else .fail .panic

/- Reused definition: aeneas-verif/v7-tag73-current-caller-source-20260830/proof/V7Tag73CurrentHelpersOpaque/FunsExternalBase.lean:245 -/
def core.array.mapListFnMut
    {T F U : Type} (fnMut : core.ops.function.FnMut F T U) :
    (values : List T) → F →
      Result ({ output : List U // output.length = values.length } × F)
  | [], closure => .ok (⟨[], rfl⟩, closure)
  | value :: rest, closure => do
      let (mapped, closureNext) ← fnMut.call_mut closure value
      let (mappedRest, closureFinal) ←
        core.array.mapListFnMut fnMut rest closureNext
      .ok (⟨mapped :: mappedRest.val, by simp [mappedRest.property]⟩,
        closureFinal)

/- Reused definition: aeneas-verif/v7-tag73-current-caller-source-20260830/proof/V7Tag73CurrentHelpersOpaque/FunsExternalBase.lean:258 -/
def core.array.Array.map
    {T F U : Type} {N : Std.Usize}
    (fnMut : core.ops.function.FnMut F T U)
    (values : Array T N) (closure : F) : Result (Array U N) := do
  let (mapped, _) ← core.array.mapListFnMut fnMut values.val closure
  .ok ⟨mapped.val, mapped.property.trans values.property⟩

/- Reused definition: aeneas-verif/v7-tag73-current-caller-source-20260830/proof/V7Tag73CurrentHelpersOpaque/FunsExternalBase.lean:267 -/
def MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter
    {T : Type} {N : Std.Usize} (array : Array T N) :
    Result (core.slice.iter.IterMut T ×
      (core.slice.iter.IterMut T → Array T N)) :=
  .ok ({ slice := Array.to_slice array },
    fun iterator => Array.from_slice array iterator.slice)

/- Reused definition: aeneas-verif/v7-tag73-current-caller-source-20260830/proof/V7Tag73CurrentHelpersOpaque/FunsExternalBase.lean:331 -/
def core.option.Option.ok_or {T E : Type} :
    Option T → E → Result (core.result.Result T E)
  | some value, _ => .ok (.Ok value)
  | none, error => .ok (.Err error)

/- Reused definition: aeneas-verif/v7-tag73-current-caller-source-20260830/proof/V7Tag73CurrentHelpersOpaque/FunsExternalBase.lean:378 -/
def core.slice.iter.Windows.windowAt
    {T : Type} (slice : Slice T) (index width : Nat) : Slice T :=
  ⟨(slice.val.drop index).take width, by
    calc
      ((slice.val.drop index).take width).length ≤
          (slice.val.drop index).length := List.length_take_le' _ _
      _ = slice.val.length - index := List.length_drop
      _ ≤ slice.val.length := Nat.sub_le _ _
      _ ≤ Usize.max := slice.property⟩

/- Reused definition: aeneas-verif/v7-tag73-current-caller-source-20260830/proof/V7Tag73CurrentHelpersOpaque/FunsExternalBase.lean:390 -/
def core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice.next
    {T : Type} (iterator : core.slice.iter.Windows T) :
    Result (Option (Slice T) × core.slice.iter.Windows T) :=
  if iterator.index + iterator.width.val ≤ iterator.slice.val.length then
    .ok (some (core.slice.iter.Windows.windowAt iterator.slice
      iterator.index iterator.width.val),
      { iterator with index := iterator.index + 1 })
  else .ok (none, iterator)

/- Reused definition: aeneas-verif/v7-tag73-current-caller-source-20260830/proof/V7Tag73CurrentHelpersOpaque/FunsExternalBase.lean:401 -/
def core.slice.iter.Iter.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedT.next_back
    {T : Type} (iterator : core.slice.iter.Iter T) :
    Result (Option T × core.slice.iter.Iter T) :=
  if iterator.i < iterator.slice.val.length then
    let shortened : Slice T :=
      ⟨iterator.slice.val.dropLast,
        by
          rw [List.length_dropLast]
          exact Nat.le_trans (Nat.sub_le _ _) iterator.slice.property⟩
    .ok (iterator.slice.val.getLast?, { iterator with slice := shortened })
  else
    .ok (none, iterator)

/- Reused definition: aeneas-verif/v7-tag73-current-caller-source-20260830/proof/V7Tag73CurrentHelpersOpaque/FunsExternalBase.lean:419 -/
def core.slice.Slice.windows
    {T : Type} (slice : Slice T) (width : Std.Usize) :
    Result (core.slice.iter.Windows T) :=
  if width = 0#usize then .fail .panic else .ok { slice, width, index := 0 }

/- Reused definition: aeneas-verif/v7-tag73-current-caller-source-20260830/proof/V7Tag73CurrentHelpersOpaque/FunsExternalBase.lean:539 -/
def alloc.vec.Vec.is_empty
    {T : Type} (_allocator : Type) (value : alloc.vec.Vec T) : Result Bool :=
  .ok value.val.isEmpty

/- Reused definition: aeneas-verif/v7-registry-v2-production-call-composition-20260831/generated/V7PairForestProductionCodecs/FunsExternal.lean:21 -/
def Slice.Insts.CoreCmpPartialEqArray.eq
    {T U : Type} {N : Std.Usize}
    (partialEq : core.cmp.PartialEq T U) :
    Slice T → Array U N → Result Bool :=
  fun left right =>
    core.slice.cmp.PartialEqSlice.eq partialEq left right.to_slice

def Slice.Insts.CoreCmpPartialEqArray.ne {T U : Type} {N : Usize}
    (eq : core.cmp.PartialEq T U) (a : Slice T) (b : Array U N) : Result Bool := do
  let same ← Slice.Insts.CoreCmpPartialEqArray.eq eq a b
  ok (!same)

/- Reused definition: aeneas-verif/v7-registry-v2-production-call-composition-20260831/generated/V7PairForestProductionCodecs/FunsExternal.lean:74 -/
def core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.any
    {T F : Type} (fnMut : core.ops.function.FnMut F T Bool) :
    core.slice.iter.Iter T → F →
      Result (Bool × core.slice.iter.Iter T) :=
  core.iter.traits.iterator.Iterator.any.default
    (core.iter.traits.iterator.IteratorSliceIter T) fnMut

/- Reused definition: aeneas-verif/v7-registry-v2-production-call-composition-20260831/generated/V7PairForestProductionCodecs/FunsExternal.lean:83 -/
def core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.all
    {T F : Type} (fnMut : core.ops.function.FnMut F T Bool) :
    core.slice.iter.Iter T → F →
      Result (Bool × core.slice.iter.Iter T) :=
  core.iter.traits.iterator.Iterator.all.default
    (core.iter.traits.iterator.IteratorSliceIter T) fnMut

/- Reused definition: aeneas-verif/v7-tag73-current-caller-source-20260830/proof/V7Tag73CurrentHelpersOpaque/FunsExternalBase.lean:572 -/
def core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.fold
    {T B F : Type} (fnMut : core.ops.function.FnMut F (B × T) B) :
    core.slice.iter.Iter T → B → F → Result B :=
  core.iter.traits.iterator.Iterator.fold.default
    (core.iter.traits.iterator.IteratorSliceIter T) fnMut

/- Reused definition: aeneas-verif/v7-tag73-current-caller-source-20260830/proof/V7Tag73CurrentHelpersOpaque/FunsExternalBase.lean:580 -/
def core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT.any
    {T F : Type} (fnMut : core.ops.function.FnMut F T Bool)
    (iterator : core.slice.iter.IterMut T) (closure : F) :
    Result (Bool × core.slice.iter.IterMut T ×
      (core.slice.iter.IterMut T → core.slice.iter.IterMut T)) := do
  let result ← core.iter.traits.iterator.Iterator.any.default
    { next := fun state => do
        let (item, next, _) ← core.slice.iter.IteratorIterMut.next state
        .ok (item, next) }
    fnMut iterator closure
  .ok (result.1, result.2, fun state => state)

/- Reused definition: aeneas-verif/v7-tag73-current-caller-source-20260830/proof/V7Tag73CurrentHelpersOpaque/FunsExternalBase.lean:594 -/
def core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT.fold
    {T B F : Type} (fnMut : core.ops.function.FnMut F (B × T) B)
    (iterator : core.slice.iter.IterMut T) (accumulator : B) (closure : F) :
    Result (B × core.slice.iter.IterMut T) := do
  let result : B × core.slice.iter.IterMut T × F ←
    loop
      (fun (acc, state, closureState) => do
        let (item, stateNext, _) ← core.slice.iter.IteratorIterMut.next state
        match item with
        | none => .ok (.done (acc, stateNext, closureState))
        | some value =>
          let (accNext, closureNext) ←
            fnMut.call_mut closureState (acc, value)
          .ok (.cont (accNext, stateNext, closureNext)))
      (accumulator, iterator, closure)
  .ok (result.1, result.2.1)

/- Reused definition: aeneas-verif/v7-tag73-selected-pool-callers-current/generated/V7Tag73SelectedSemanticLoopForm/FunsExternal.lean:163 -/
def core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.fold
  {I : Type} {Acc : Type} {F : Type} {Clause0_Clause0_Item : Type}
  (traitsdouble_endedDoubleEndedIteratorInst :
  core.iter.traits.double_ended.DoubleEndedIterator I Clause0_Clause0_Item)
  (opsfunctionFnMutFPairAccInst : core.ops.function.FnMut F (Acc ×
  Clause0_Clause0_Item) Acc) (iterator : core.iter.adapters.rev.Rev I)
  (accumulator : Acc) (closure : F) : Result Acc := do
  let result : Acc × core.iter.adapters.rev.Rev I × F ←
    loop
      (fun (acc, state, closureState) => do
        let (item, innerNext) ←
          traitsdouble_endedDoubleEndedIteratorInst.next_back state.iter
        match item with
        | none => .ok (.done (acc, ⟨innerNext⟩, closureState))
        | some value =>
          let (accNext, closureNext) ←
            opsfunctionFnMutFPairAccInst.call_mut closureState (acc, value)
          .ok (.cont (accNext, ⟨innerNext⟩, closureNext)))
      (accumulator, iterator, closure)
  .ok result.1

/- Specialization of the pinned Aeneas iterator/default model; original
 signature is the emitted external signature. No result assumption. -/
def core.iter.traits.iterator.Iterator.map.default
  {Self : Type} {B : Type} {F : Type} {Clause0_Item : Type} (IteratorInst :
  core.iter.traits.iterator.Iterator Self Clause0_Item)
  (opsfunctionFnMutFTupleClause0_ItemBInst : core.ops.function.FnMut F
  Clause0_Item B) :
  Self → F → Result (core.iter.adapters.map.Map Self F) :=
  fun self f => ok ⟨self, f⟩

/- Specialization of the pinned Aeneas iterator/default model; original
 signature is the emitted external signature. No result assumption. -/
def core.result.Result.unwrap_or_else
  {T : Type} {E : Type} {F : Type} (opsfunctionFnOnceFTupleETInst :
  core.ops.function.FnOnce F E T) :
  (core.result.Result T E) → F → Result T :=
  fun self f => match self with
    | .Ok x => ok x
    | .Err e => opsfunctionFnOnceFTupleETInst.call_once f e

/- Specialization of the pinned Aeneas iterator/default model; original
 signature is the emitted external signature. No result assumption. -/
def core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.any
  {A : Type} {F : Type} (StepInst : core.iter.range.Step A)
  (opsfunctionFnMutFTupleABoolInst : core.ops.function.FnMut F A Bool) :
  (core.ops.range.Range A) → F → Result (Bool × (core.ops.range.Range A)) :=
  core.iter.traits.iterator.Iterator.any.default (core.iter.traits.iterator.IteratorRange StepInst) opsfunctionFnMutFTupleABoolInst

/- Specialization of the pinned Aeneas iterator/default model; original
 signature is the emitted external signature. No result assumption. -/
def core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.all
  {A : Type} {F : Type} (StepInst : core.iter.range.Step A)
  (opsfunctionFnMutFTupleABoolInst : core.ops.function.FnMut F A Bool) :
  (core.ops.range.Range A) → F → Result (Bool × (core.ops.range.Range A)) :=
  core.iter.traits.iterator.Iterator.all.default (core.iter.traits.iterator.IteratorRange StepInst) opsfunctionFnMutFTupleABoolInst

/- Specialization of the pinned Aeneas iterator/default model; original
 signature is the emitted external signature. No result assumption. -/
def core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.fold
  {A : Type} {B : Type} {F : Type} (StepInst : core.iter.range.Step A)
  (opsfunctionFnMutFPairBInst : core.ops.function.FnMut F (B × A) B) :
  (core.ops.range.Range A) → B → F → Result B :=
  core.iter.traits.iterator.Iterator.fold.default (core.iter.traits.iterator.IteratorRange StepInst) opsfunctionFnMutFPairBInst

/- Specialization of the pinned Aeneas iterator/default model; original
 signature is the emitted external signature. No result assumption. -/
def core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.collect
  {A : Type} {B : Type} (StepInst : core.iter.range.Step A)
  (traitscollectFromIteratorInst : core.iter.traits.collect.FromIterator B A) :
  (core.ops.range.Range A) → Result B :=
  core.iter.traits.iterator.Iterator.collect.default (core.iter.traits.iterator.IteratorRange StepInst) traitscollectFromIteratorInst

/- Specialization of the pinned Aeneas iterator/default model; original
 signature is the emitted external signature. No result assumption. -/
def core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.rev
  {A : Type} {Clause1_Clause0_Item : Type} (StepInst : core.iter.range.Step A)
  (traitsdouble_endedDoubleEndedIteratorRangeClause1_Clause0_ItemInst :
  core.iter.traits.double_ended.DoubleEndedIterator (core.ops.range.Range A)
  Clause1_Clause0_Item) :
  (core.ops.range.Range A) → Result (core.iter.adapters.rev.Rev
    (core.ops.range.Range A)) :=
  core.iter.traits.iterator.Iterator.rev.default

/- Specialization of the pinned Aeneas iterator/default model; original
 signature is the emitted external signature. No result assumption. -/
def core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.enumerate
  {A : Type} (StepInst : core.iter.range.Step A) :
  (core.ops.range.Range A) → Result (core.iter.adapters.enumerate.Enumerate
    (core.ops.range.Range A)) :=
  core.iter.traits.iterator.Iterator.enumerate.default

/- Specialization of the pinned Aeneas iterator/default model; original
 signature is the emitted external signature. No result assumption. -/
def core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.map
  {A : Type} {B : Type} {F : Type} (StepInst : core.iter.range.Step A)
  (opsfunctionFnMutFTupleABInst : core.ops.function.FnMut F A B) :
  (core.ops.range.Range A) → F → Result (core.iter.adapters.map.Map
    (core.ops.range.Range A) F) :=
  fun self f => ok ⟨self, f⟩

/- Specialization of the pinned Aeneas iterator/default model; original
 signature is the emitted external signature. No result assumption. -/
def core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.step_by
  {A : Type} (StepInst : core.iter.range.Step A) :
  (core.ops.range.Range A) → Std.Usize → Result
    (core.iter.adapters.step_by.StepBy (core.ops.range.Range A)) :=
  core.iter.traits.iterator.Iterator.step_by.default

/- Specialization of the pinned Aeneas iterator/default model; original
 signature is the emitted external signature. No result assumption. -/
def core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.rev
  {T : Type} {Clause0_Clause0_Item : Type}
  (itertraitsdouble_endedDoubleEndedIteratorIterClause0_Clause0_ItemInst :
  core.iter.traits.double_ended.DoubleEndedIterator (core.slice.iter.Iter T)
  Clause0_Clause0_Item) :
  (core.slice.iter.Iter T) → Result (core.iter.adapters.rev.Rev
    (core.slice.iter.Iter T)) :=
  core.iter.traits.iterator.Iterator.rev.default

/- Specialization of the pinned Aeneas iterator/default model; original
 signature is the emitted external signature. No result assumption. -/
def
  core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.enumerate
  {T : Type} :
  (core.slice.iter.Iter T) → Result (core.iter.adapters.enumerate.Enumerate
    (core.slice.iter.Iter T)) :=
  core.iter.traits.iterator.Iterator.enumerate.default

/- Specialization of the pinned Aeneas iterator/default model; original
 signature is the emitted external signature. No result assumption. -/
def core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.map
  {T : Type} {B : Type} {F : Type} (opsfunctionFnMutFTupleSharedATBInst :
  core.ops.function.FnMut F T B) :
  (core.slice.iter.Iter T) → F → Result (core.iter.adapters.map.Map
    (core.slice.iter.Iter T) F) :=
  fun self f => ok ⟨self, f⟩

/- Specialization of the pinned Aeneas iterator/default model; original
 signature is the emitted external signature. No result assumption. -/
def core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.step_by
  {T : Type} :
  (core.slice.iter.Iter T) → Std.Usize → Result
    (core.iter.adapters.step_by.StepBy (core.slice.iter.Iter T)) :=
  core.iter.traits.iterator.Iterator.step_by.default

/- Specialization of the pinned Aeneas iterator/default model; original
 signature is the emitted external signature. No result assumption. -/
def core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.collect
  {T : Type} {B : Type} (itertraitscollectFromIteratorBSharedATInst :
  core.iter.traits.collect.FromIterator B T) :
  (core.slice.iter.Iter T) → Result B :=
  core.iter.traits.iterator.Iterator.collect.default (core.iter.traits.iterator.IteratorSliceIter T) itertraitscollectFromIteratorBSharedATInst

/- Specialization of the pinned Aeneas iterator/default model; original
 signature is the emitted external signature. No result assumption. -/
def
  core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice.all
  {T : Type} {F : Type} (opsfunctionFnMutFTupleSharedASliceBoolInst :
  core.ops.function.FnMut F (Slice T) Bool) :
  (core.slice.iter.Windows T) → F → Result (Bool ×
    (core.slice.iter.Windows T)) :=
  core.iter.traits.iterator.Iterator.all.default { next := core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice.next } opsfunctionFnMutFTupleSharedASliceBoolInst

namespace XRj_Bytes
/- XRe_reference.rs:28-38: little-endian words at 4*j, then canonical test.
   XRg_reference.rs:validate_reference: same eight-word test, high half zero.
   Complete 16/32-byte chunks only; the tail is intentionally ignored. -/
def le32 (bs : List U8) : Nat :=
  (bs.take 4).foldr (fun b n => b.val + 256*n) 0

def validChunk (width : Nat) (highZero : Bool) (bs : List U8) : Bool :=
  (List.range width).all fun j =>
    let n := le32 ((bs.drop (4*j)).take 4)
    decide (n < 2147483647) && (!highZero || decide (j < 4 ∨ n = 0))

def chunksValid (size width : Nat) (highZero : Bool) (bs : List U8) : Bool :=
  (List.range (bs.length / size)).all fun i =>
    validChunk width highZero ((bs.drop (size*i)).take size)
end XRj_Bytes

/- P6 OPEN. XRe_reference.rs:28-38, lines 29/30 loop bound -> chunksValid16;
   lines31-33 word parse/test -> validChunk4; lines35-38 -> error/Ok. -/
def compact.check_values (bytes : Slice U8) :
    Result (core.result.Result Unit compact.CodecError) :=
  ok (if XRj_Bytes.chunksValid 16 4 false bytes.val then .Ok () else .Err .NonCanonical)

/- P6 OPEN. XRe_reference.rs:49-60, lines50-51 chunk loop -> chunksValid32;
   lines52-55 parse8/canonical/high-zero -> validChunk8; lines56-60 -> return. -/
def verifier.echeck (bytes : Slice U8) (k : Bool) :
    Result (core.result.Result Unit verifier.Error) :=
  ok (if XRj_Bytes.chunksValid 32 8 k bytes.val then .Ok () else .Err .Parse)

/- P6 OPEN. XRg_reference.rs:validate_reference, whole chunks32 in source order;
   first failing chunk i yields NonCanonical(row,i), matching the reference. -/
def r1_wire.validate_record_fields (row : U8) (bytes : Slice U8) :
    Result (core.result.Result Unit r1_wire.Error) := do
  match (List.range (bytes.val.length / 32)).find? (fun i =>
      !(XRj_Bytes.validChunk 8 true ((bytes.val.drop (32*i)).take 32))) with
  | none => ok (.Ok ())
  | some i =>
    let index ← lift (UScalar.ofNat .Usize i)
    ok (.Err (.NonCanonical row index))

/- P6 OPEN. XRe_reference.rs:39-47: alignment short-circuits first; checked
   multiplication matches Rust's overflow behavior. Source low16 copy / high16
   fill is the map on every destination index. No allocator/borrow bridge. -/
def compact.expand_values (bytes out : Slice U8) :
    Result ((core.result.Result Unit compact.CodecError) × Slice U8) := do
  if bytes.val.length % 16 != 0 then
    ok (.Err .Length, out)
  else
    let size ← Slice.len bytes * 2#usize
    if Slice.len out != size then ok (.Err .Length, out)
    else
      let values := (List.range out.val.length).map fun i =>
        if i % 32 < 16 then bytes.val[i/32*16+i%32]?.getD 0#u8 else 0#u8
      match out with
      | ⟨_, bound⟩ =>
        ok (.Ok (), ⟨values, by simpa [values] using bound⟩)
