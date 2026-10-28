import R1Z.BuilderStdCollect
import R1Z.BuilderAdmissionStd

/-! Executable std adapters for the forest extraction. Iterator operations
preserve error order and short-circuit state. These definitions replace std
externals only, not the three opaque Aspis declarations. -/
set_option autoImplicit false
namespace R1Z.BuilderForestStd
open Aeneas Aeneas.Std Result
variable {T U E V C I A B : Type}

abbrev IntoIter (T : Type) (_n : Std.Usize) := List T
def intoIter {n : Std.Usize} (a : Array T n) : Result (IntoIter T n) := ok a.val
def arrayNext {n : Std.Usize} (it : IntoIter T n) : Result (Option T × IntoIter T n) :=
  match it with
  | [] => ok (none,[])
  | x::xs => ok (some x,xs)

structure Flatten (I A B U : Type) where
  outer : I
  inner : Option U

def flatten (it : core.iter.traits.iterator.Iterator I A)
    (conv : core.iter.traits.collect.IntoIterator A B U) (i : I) :
    Result (Flatten I A B U) := ok ⟨i,none⟩

def flattenNext (it : core.iter.traits.iterator.Iterator I A)
    (conv : core.iter.traits.collect.IntoIterator A B U)
    (innerIt : core.iter.traits.iterator.Iterator U B) (s : Flatten I A B U) :
    Result (Option B × Flatten I A B U) := do
  match s.inner with
  | some u =>
    let (x,u') ← innerIt.next u
    match x with
    | some b => ok (some b,⟨s.outer,some u'⟩)
    | none => flattenNext it conv innerIt ⟨s.outer,none⟩
  | none =>
    let (x,i') ← it.next s.outer
    match x with
    | none => ok (none,⟨i',none⟩)
    | some a =>
      let u ← conv.into_iter a
      flattenNext it conv innerIt ⟨i',some u⟩
partial_fixpoint

def iterAny (it : core.iter.traits.iterator.Iterator I A)
    (f : core.ops.function.FnMut C A Bool) (i : I) (c : C) : Result (Bool × I) := do
  let (x,i') ← it.next i
  match x with
  | none => ok (false,i')
  | some x =>
    let (b,c') ← f.call_mut c x
    if b then ok (true,i') else iterAny it f i' c'
partial_fixpoint

def sumDefault (it : core.iter.traits.iterator.Iterator I A)
    (sum : core.iter.traits.accum.Sum B A) (i : I) : Result B := sum.sum it i

def sumLoop (it : core.iter.traits.iterator.Iterator I Std.U64)
    (i : I) (acc : Std.U64) : Result Std.U64 := do
  let (x,i') ← it.next i
  match x with
  | none => ok acc
  | some x =>
    let acc' ← acc + x
    sumLoop it i' acc'
partial_fixpoint

def sum64 (it : core.iter.traits.iterator.Iterator I Std.U64) (i : I) := sumLoop it i 0#u64

def mapLoop (f : core.ops.function.FnMut C T U) : List T → C → Result (List U × C)
  | [], c => ok ([],c)
  | x::xs, c => do
    let (y,c') ← f.call_mut c x
    let (ys,c'') ← mapLoop f xs c'
    ok (y::ys,c'')

def arrayMap {n : Std.Usize} (f : core.ops.function.FnMut C T U)
    (a : Array T n) (c : C) : Result (Array U n) := do
  let (ys,_) ← mapLoop f a.val c
  if h : ys.length = n.val then ok ⟨ys,h⟩ else .fail .panic

def okOr (o : Option T) (e : E) : Result (core.result.Result T E) :=
  ok (match o with | none => .Err e | some x => .Ok x)
def branch (o : Option T) : Result (core.ops.control_flow.ControlFlow
    (Option core.convert.Infallible) T) :=
  ok (match o with | none => .Break none | some x => .Continue x)
def residual (T : Type) (o : Option core.convert.Infallible) : Result (Option T) :=
  match o with | none => ok none | some i => nomatch i

def mapResult (f : core.ops.function.FnOnce C T U)
    (r : core.result.Result T E) (c : C) : Result (core.result.Result U E) :=
  match r with
  | .Err e => ok (.Err e)
  | .Ok x => do let y ← f.call_once c x; ok (.Ok y)

structure Chunks (T : Type) where
  remaining : Slice T
  size : Nat

def chunks (s : Slice T) (n : Std.Usize) : Result (Chunks T) :=
  if n.val = 0 then .fail .panic else ok ⟨s,n.val⟩

def chunksNext (s : Chunks T) : Result (Option (Slice T) × Chunks T) :=
  if s.remaining.val.isEmpty then ok (none,s)
  else
    let head : Slice T := ⟨s.remaining.val.take s.size,
      by have := s.remaining.property; simp only [List.length_take]; omega⟩
    let tail : Slice T := ⟨s.remaining.val.drop s.size,
      by have := s.remaining.property; simp only [List.length_drop]; omega⟩
    ok (some head,⟨tail,s.size⟩)

theorem intoIter_spec {n : Std.Usize} (a : Array T n) : intoIter a = ok a.val := rfl
theorem arrayNext_nil {n : Std.Usize} : arrayNext (n := n) ([] : List T) = ok (none,[]) := rfl
theorem arrayNext_cons {n : Std.Usize} (x : T) (xs : List T) :
    arrayNext (n := n) (x::xs) = ok (some x,xs) := rfl

theorem flatten_spec (it : core.iter.traits.iterator.Iterator I A)
    (conv : core.iter.traits.collect.IntoIterator A B U) (i : I) :
    flatten it conv i = ok ⟨i,none⟩ := rfl

theorem flattenNext_yield (it : core.iter.traits.iterator.Iterator I A)
    (conv : core.iter.traits.collect.IntoIterator A B U)
    (innerIt : core.iter.traits.iterator.Iterator U B) (i : I) (u u' : U) (b : B)
    (h : innerIt.next u = ok (some b,u')) :
    flattenNext it conv innerIt ⟨i,some u⟩ = ok (some b,⟨i,some u'⟩) := by
  rw [flattenNext]
  dsimp only [Flatten.inner, Flatten.outer]
  rw [h]; rfl

theorem flattenNext_skip (it : core.iter.traits.iterator.Iterator I A)
    (conv : core.iter.traits.collect.IntoIterator A B U)
    (innerIt : core.iter.traits.iterator.Iterator U B) (i : I) (u u' : U)
    (h : innerIt.next u = ok (none,u')) :
    flattenNext it conv innerIt ⟨i,some u⟩ = flattenNext it conv innerIt ⟨i,none⟩ := by
  rw [flattenNext]
  dsimp only [Flatten.inner, Flatten.outer]
  rw [h]; rfl

theorem flattenNext_done (it : core.iter.traits.iterator.Iterator I A)
    (conv : core.iter.traits.collect.IntoIterator A B U)
    (innerIt : core.iter.traits.iterator.Iterator U B) (i i' : I)
    (h : it.next i = ok (none,i')) :
    flattenNext it conv innerIt ⟨i,none⟩ = ok (none,⟨i',none⟩) := by
  rw [flattenNext]
  dsimp only [Flatten.inner, Flatten.outer]
  rw [h]; rfl

theorem flattenNext_open (it : core.iter.traits.iterator.Iterator I A)
    (conv : core.iter.traits.collect.IntoIterator A B U)
    (innerIt : core.iter.traits.iterator.Iterator U B) (i i' : I) (a : A) (u : U)
    (h : it.next i = ok (some a,i')) (hc : conv.into_iter a = ok u) :
    flattenNext it conv innerIt ⟨i,none⟩ = flattenNext it conv innerIt ⟨i',some u⟩ := by
  rw [flattenNext,h]; simp only [bind_tc_ok]; rw [hc]; rfl

theorem any_done (it : core.iter.traits.iterator.Iterator I A)
    (f : core.ops.function.FnMut C A Bool) (i i' : I) (c : C)
    (h : it.next i = ok (none,i')) : iterAny it f i c = ok (false,i') := by
  rw [iterAny,h]; rfl

theorem any_stop (it : core.iter.traits.iterator.Iterator I A)
    (f : core.ops.function.FnMut C A Bool) (i i' : I) (c c' : C) (a : A)
    (h : it.next i = ok (some a,i')) (hf : f.call_mut c a = ok (true,c')) :
    iterAny it f i c = ok (true,i') := by
  rw [iterAny,h]; simp only [bind_tc_ok]; rw [hf]; rfl

theorem any_continue (it : core.iter.traits.iterator.Iterator I A)
    (f : core.ops.function.FnMut C A Bool) (i i' : I) (c c' : C) (a : A)
    (h : it.next i = ok (some a,i')) (hf : f.call_mut c a = ok (false,c')) :
    iterAny it f i c = iterAny it f i' c' := by
  rw [iterAny,h]; simp only [bind_tc_ok]; rw [hf]; rfl

theorem sumDefault_spec (it : core.iter.traits.iterator.Iterator I A)
    (sum : core.iter.traits.accum.Sum B A) (i : I) : sumDefault it sum i = sum.sum it i := rfl

theorem sum_done (it : core.iter.traits.iterator.Iterator I Std.U64)
    (i i' : I) (acc : Std.U64) (h : it.next i = ok (none,i')) :
    sumLoop it i acc = ok acc := by rw [sumLoop,h]; rfl

theorem sum_step (it : core.iter.traits.iterator.Iterator I Std.U64)
    (i i' : I) (acc x acc' : Std.U64) (h : it.next i = ok (some x,i'))
    (ha : acc + x = ok acc') : sumLoop it i acc = sumLoop it i' acc' := by
  rw [sumLoop,h]; simp only [bind_tc_ok]; rw [ha]; rfl

theorem mapLoop_pure (f : core.ops.function.FnMut C T U) (g : T → U)
    (hf : ∀ c x, f.call_mut c x = ok (g x,c)) (xs : List T) (c : C) :
    mapLoop f xs c = ok (xs.map g,c) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [mapLoop,hf,ih]

theorem arrayMap_pure {n : Std.Usize} (f : core.ops.function.FnMut C T U)
    (g : T → U) (hf : ∀ c x, f.call_mut c x = ok (g x,c)) (a : Array T n) (c : C) :
    arrayMap f a c = ok ⟨a.val.map g, by simp [a.property]⟩ := by
  simp [arrayMap,mapLoop_pure f g hf,a.property]

theorem okOr_none (e : E) : okOr (none : Option T) e = ok (.Err e) := rfl
theorem okOr_some (x : T) (e : E) : okOr (some x) e = ok (.Ok x) := rfl
theorem branch_none : branch (none : Option T) = ok (.Break none) := rfl
theorem branch_some (x : T) : branch (some x) = ok (.Continue x) := rfl
theorem residual_none : residual T none = ok none := rfl

theorem mapResult_err (f : core.ops.function.FnOnce C T U) (e : E) (c : C) :
    mapResult f (.Err e) c = ok (.Err e) := rfl
theorem mapResult_ok (f : core.ops.function.FnOnce C T U) (x : T) (c : C) :
    mapResult f (.Ok x : core.result.Result T E) c =
      (do let y ← f.call_once c x; ok (.Ok y)) := rfl

theorem chunks_zero (s : Slice T) : chunks s 0#usize = .fail .panic := by
  simp [chunks]
theorem chunks_positive (s : Slice T) (n : Std.Usize) (hn : n.val ≠ 0) :
    chunks s n = ok ⟨s,n.val⟩ := by simp [chunks,hn]
theorem chunksNext_empty (s : Chunks T) (h : s.remaining.val.isEmpty = true) :
    chunksNext s = ok (none,s) := by simp [chunksNext,h]

theorem chunksNext_content (s : Chunks T) (h : s.remaining.val.isEmpty = false) :
    ∃ head tail, chunksNext s = ok (some head,tail) ∧
      head.val = s.remaining.val.take s.size ∧
      tail.remaining.val = s.remaining.val.drop s.size ∧ tail.size = s.size := by
  simp only [chunksNext,h,Bool.false_eq_true,↓reduceIte]
  exact ⟨_,_,rfl,rfl,rfl,rfl⟩

#print axioms intoIter_spec
#print axioms arrayNext_nil
#print axioms arrayNext_cons
#print axioms flatten_spec
#print axioms flattenNext_yield
#print axioms flattenNext_skip
#print axioms flattenNext_done
#print axioms flattenNext_open
#print axioms any_done
#print axioms any_stop
#print axioms any_continue
#print axioms sumDefault_spec
#print axioms sum_done
#print axioms sum_step
#print axioms mapLoop_pure
#print axioms arrayMap_pure
#print axioms okOr_none
#print axioms okOr_some
#print axioms branch_none
#print axioms branch_some
#print axioms residual_none
#print axioms mapResult_err
#print axioms mapResult_ok
#print axioms chunks_zero
#print axioms chunks_positive
#print axioms chunksNext_empty
#print axioms chunksNext_content
end R1Z.BuilderForestStd
