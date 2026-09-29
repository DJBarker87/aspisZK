import AspisV8R19.QuarticFieldSlice
import Aeneas.Std.Array.Array
import Aeneas.Std.SliceIter
import Aeneas.Std.Core.Ops

/-! Concrete library models replacing R67's rejected templates. These are
definitions, not axioms. Array/slice/chain callback semantics are explicit.
`Iterator.any.default` uses next-based traversal; source correspondence for
Rust's specialized `try_fold` must be proved at the concrete call site, not
assumed for arbitrary user implementations of Iterator. Drop/unwind observations
are outside the retained Aeneas Result model. -/
set_option autoImplicit false
namespace AspisV8R19.TraversalRuntime
open Aeneas Aeneas.Std Result ControlFlow

def mapState {T U F : Type} (call : F → T → Result (U × F)) :
    List T → F → Result (List U × F)
  | [], state => .ok ([],state)
  | x::xs, state => do
    let (y,state') ← call state x
    let (ys,state'') ← mapState call xs state'
    .ok (y::ys,state'')

theorem mapState_length {T U F : Type} (call : F → T → Result (U × F))
    (xs : List T) (state : F) (ys : List U) (last : F)
    (h : mapState call xs state = .ok (ys,last)) : ys.length = xs.length := by
  induction xs generalizing state ys last with
  | nil => simp [mapState] at h; rcases h with ⟨rfl,rfl⟩; rfl
  | cons x xs ih =>
    simp only [mapState] at h
    cases hc : call state x with
    | fail e => simp [hc] at h
    | div => simp [hc] at h
    | ok pair =>
      rcases pair with ⟨y,state'⟩
      cases hm : mapState call xs state' with
      | fail e => simp [hc,hm] at h
      | div => simp [hc,hm] at h
      | ok pair =>
        rcases pair with ⟨tail,state''⟩
        simp only [hc,hm,bind_tc_ok,Result.ok.injEq,Prod.mk.injEq] at h
        rcases h with ⟨rfl,rfl⟩
        simp only [List.length_cons,ih _ _ _ hm]

#print axioms mapState_length

def anyBody {I T F : Type} (next : I → Result (Option T × I))
    (call : F → T → Result (Bool × F)) (state : I × F) :
    Result (ControlFlow (I × F) (Bool × I)) := do
  let (item,iter) ← next state.1
  match item with
  | none => .ok (.done (false,iter))
  | some x =>
    let (hit,callback) ← call state.2 x
    if hit then .ok (.done (true,iter)) else .ok (.cont (iter,callback))

def anyRun {I T F : Type} (next : I → Result (Option T × I))
    (call : F → T → Result (Bool × F)) (iter : I) (callback : F) : Result (Bool × I) :=
  loop (anyBody next call) (iter,callback)

end AspisV8R19.TraversalRuntime

namespace Aeneas.Std
open Result
open AspisV8R19.TraversalRuntime

structure core.iter.adapters.chain.Chain (A B : Type) where
  a : Option A
  b : Option B

def core.iter.traits.iterator.Iterator.chain.default
    {Self U Item IntoIter : Type}
    (_iterator : core.iter.traits.iterator.Iterator Self Item)
    (into : core.iter.traits.collect.IntoIterator U Item IntoIter)
    (self : Self) (other : U) : Result (core.iter.adapters.chain.Chain Self IntoIter) := do
  let right ← into.into_iter other
  .ok ⟨some self,some right⟩

def core.iter.adapters.chain.rightNext {A B Item : Type}
    (right : core.iter.traits.iterator.Iterator B Item)
    (self : core.iter.adapters.chain.Chain A B) :
    Result (Option Item × core.iter.adapters.chain.Chain A B) := do
  match self.b with
  | none => .ok (none,self)
  | some b =>
    let (item,b') ← right.next b
    .ok (item,{self with b := some b'})

def core.iter.adapters.chain.Chain.Insts.CoreIterTraitsIteratorIterator.next
    {A B Item : Type} (left : core.iter.traits.iterator.Iterator A Item)
    (right : core.iter.traits.iterator.Iterator B Item)
    (self : core.iter.adapters.chain.Chain A B) :
    Result (Option Item × core.iter.adapters.chain.Chain A B) := do
  match self.a with
  | none => core.iter.adapters.chain.rightNext right self
  | some a =>
    let (item,a') ← left.next a
    match item with
    | some x => .ok (some x,{self with a := some a'})
    | none => core.iter.adapters.chain.rightNext right {self with a := none}

def core.iter.traits.iterator.Iterator.any.default
    {Self F Item : Type} (iter : core.iter.traits.iterator.Iterator Self Item)
    (callback : core.ops.function.FnMut F Item Bool)
    (self : Self) (f : F) : Result (Bool × Self) :=
  anyRun iter.next callback.call_mut self f

def core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.any
    {T F : Type} (callback : core.ops.function.FnMut F T Bool)
    (self : core.slice.iter.Iter T) (f : F) : Result (Bool × core.slice.iter.Iter T) :=
  anyRun core.slice.iter.IteratorSliceIter.next callback.call_mut self f

def core.array.Array.map {T F U : Type} {N : Usize}
    (callback : core.ops.function.FnMut F T U) (self : Array T N) (f : F) :
    Result (Array U N) :=
  match h : mapState callback.call_mut self.val f with
  | .ok (ys,_last) => .ok ⟨ys,(mapState_length _ _ _ _ _ h).trans self.property⟩
  | .fail e => .fail e
  | .div => .div

def core.option.Option.ok_or {T E : Type} (self : Option T) (err : E) :
    Result (core.result.Result T E) :=
  match self with
  | some value => .ok (.Ok value)
  | none => .ok (.Err err)

end Aeneas.Std
