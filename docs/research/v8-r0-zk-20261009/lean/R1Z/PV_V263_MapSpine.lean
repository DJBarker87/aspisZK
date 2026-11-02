import R1Z.PV_V263_DeferredJoin
import R1Z.PV_V263_Family
/-! Candidate source spine for ONE explicit scheduling witness (join-late).
This is not yet a V263 native association or an opsNative installation.
Vector methods are stateful effects with list data flow; their std lowering,
heap/drop semantics and event codec remain native obligations. Callback values
are computed by the supplied stateful code, not answered by a worker oracle.
The selected profile is the deployed panic=abort profile. -/
set_option autoImplicit false
namespace R1Z.PV_V263_MapSpine
open Aeneas Aeneas.Std PV_V263_World PV_V263_WorkerRequests PV_V263_WorkerControl
open PV_V263_PublicRequests (Layout)
open PV_RJ4IDB (Bytes)

/-- Source METHOD calls, not raw allocator syscalls. Site identifiers:
0 inner item Vec;1 one-family collect;2 handles;3 caught chunks;4 pool output;
5 host_work output. Lengths/layouts must be lowered under V400-257. -/
inductive VecCall where
  | empty (site thread : Nat) (layout : Layout)
  | capacity (site thread elements : Nat) (layout : Layout)
  | collect (site thread elements : Nat) (layout : Layout)
  | push (site thread oldLength : Nat) (layout : Layout)
  | append (site thread oldLength added : Nat) (layout : Layout)
  | drop (site thread : Nat) (layout : Layout)

structure Layouts where
  item : Layout
  family : Layout
  caught : Layout
  handle : Layout

structure Runtime (S : Type) where
  os : PV_V263_WorkerRequests.Runtime S
  vector : VecCall → Q S Unit

local instance {S : Type} : Monad (Q S) where
  pure a := PV_V263_World.lift (.ok a)
  bind := PV_V263_World.bind

/-- The callback loop has no cancellation on a returned inner Rust Err. -/
def items {S A : Type} (runtime : Runtime S) (layouts : Layouts) (n k : Nat)
    (callback : Nat → Q S A) : Q S (List A) := do
  runtime.vector (.capacity 0 k (PV_RunJoin_WorkRange35.width n k) layouts.item)
  PV_V263_WorkerControl.traverse callback (PV_V263_Family.indices n k)

/-- The outer pool range is one family. collect has its own allocation/drop
behaviour, distinct from that family's item vector. completed is public width
on success; there is no whole-worker result answer. -/
def family {S A : Type} (runtime : Runtime S) (layouts : Layouts) (n k : Nat)
    (callback : Nat → Q S A) : Q S (List (List A × Nat)) := do
  runtime.vector (.collect 1 k 1 layouts.family)
  let values ← items runtime layouts n k callback
  pure [(values,values.length)]

def caughtFamily {S A : Type} (runtime : Runtime S) (layouts : Layouts) (n k : Nat)
    (callback : Nat → Q S A) : Q S (Except Bytes (List (List A × Nat))) :=
  withActive runtime.os .abort k (catchPanic .abort (family runtime layouts n k callback))

/-- Scope's spawn loop precedes caller run(0); the scheduler witness defers all
child code until its join. Each handles push remains an effect-capable method. -/
def forks {S A : Type} (runtime : Runtime S) (layouts : Layouts) (n : Nat)
    (callback : Nat → Q S A) : Q S (List (PV_V263_DeferredJoin.Task S (List (List A × Nat)))) :=
  PV_V263_WorkerControl.traverse (fun k => do
    let task ← PV_V263_DeferredJoin.fork runtime.os k (caughtFamily runtime layouts n k callback)
    runtime.vector (.push 2 0 (k-1) layouts.handle)
    pure task) (List.range' 1 15)

def joinChunks {S A : Type} (runtime : Runtime S) (layouts : Layouts) :
    Nat → List (PV_V263_DeferredJoin.Task S (List (List A × Nat))) →
    Q S (List (Except Bytes (List (List A × Nat))))
  | _,[] => pure []
  | length,task::rest => do
    let caught ← PV_V263_DeferredJoin.join runtime.os task
    runtime.vector (.push 3 0 length layouts.caught)
    let others ← joinChunks runtime layouts (length+1) rest
    pure (caught::others)

/-- This stage resumes the first source-order panic AFTER all handles joined.
The partial append/drop event prefix is retained if a later chunk panics. -/
def mergePool {S A : Type} (runtime : Runtime S) (layouts : Layouts) :
    Nat → List (Except Bytes (List (List A × Nat))) → Q S (List (List A × Nat))
  | _,[] => pure []
  | _,.error p::_ => fun w => ⟨.fault (.abort p),w,[]⟩
  | length,.ok chunk::rest => do
    runtime.vector (.append 4 0 length chunk.length layouts.family)
    runtime.vector (.drop 1 length layouts.family)
    let others ← mergePool runtime layouts (length+chunk.length) rest
    pure (chunk++others)

def pool {S A : Type} (runtime : Runtime S) (layouts : Layouts) (n : Nat)
    (callback : Nat → Q S A) : Q S (List (List A × Nat)) := do
  let active ← runtime.os.answer (.tlsRead 0)
  if active then do
    runtime.vector (.collect 4 0 16 layouts.family)
    let chunks ← PV_V263_WorkerControl.traverse (fun k => do
      let values ← items runtime layouts n k callback
      pure (values,values.length)) (List.range 16)
    pure chunks
  else
    withActive runtime.os .abort 0 (do
      runtime.vector (.empty 2 0 layouts.handle)
      let handles ← forks runtime layouts n callback
      let first ← caughtFamily runtime layouts n 0 callback
      runtime.vector (.capacity 3 0 16 layouts.caught)
      runtime.vector (.push 3 0 0 layouts.caught)
      let others ← joinChunks runtime layouts 1 handles
      runtime.vector (.drop 2 0 layouts.handle)
      runtime.os.answer (.cleanup 0)
      runtime.vector (.capacity 4 0 16 layouts.family)
      let values ← mergePool runtime layouts 0 (first::others)
      runtime.vector (.drop 3 0 layouts.caught)
      pure values)

def appendItems {S A : Type} (runtime : Runtime S) (layouts : Layouts) :
    Nat → Nat → List (List A × Nat) → Q S (List A)
  | _,_,[] => pure []
  | length,k,(chunk,_)::rest => do
    runtime.vector (.append 5 0 length chunk.length layouts.item)
    runtime.vector (.drop 0 k layouts.item)
    let others ← appendItems runtime layouts (length+chunk.length) (k+1) rest
    pure (chunk++others)

def run {S A : Type} (runtime : Runtime S) (layouts : Layouts)
    (_stage n : Nat) (callback : Nat → Q S A) : Q S (List A) := do
  let chunks ← pool runtime layouts n callback
  runtime.vector (.capacity 5 0 n layouts.item)
  let values ← appendItems runtime layouts 0 0 chunks
  runtime.vector (.drop 4 0 layouts.family)
  pure values

theorem stage_unused {S A : Type} (runtime : Runtime S) (layouts : Layouts)
    (stage stage' n : Nat) (callback : Nat → Q S A) :
    run runtime layouts stage n callback = run runtime layouts stage' n callback := rfl

#print axioms VecCall
#print axioms Layouts
#print axioms Runtime
#print axioms items
#print axioms family
#print axioms caughtFamily
#print axioms forks
#print axioms joinChunks
#print axioms mergePool
#print axioms pool
#print axioms appendItems
#print axioms run
#print axioms stage_unused
end R1Z.PV_V263_MapSpine
