import R1Z.PV_V263_VectorDrain
/-! Vec-valued source port of the frozen worker control, with explicit stored
handles, caught chunks, completed counters, draining appends and iterator/drop
lifetime hooks. This is a source port, not an extraction or native association.
The physical method/lifetime codec and schedule realisation remain unbound.
No fault is coerced to a source Result at the dictionary boundary. -/
set_option autoImplicit false
namespace R1Z.PV_V263_VecSpine
open Aeneas Aeneas.Std PV_V263_World PV_V263_WorkerRequests PV_V263_WorkerControl
open PV_RJ4IDB (Bytes)
abbrev Layouts := PV_V263_MapSpine.Layouts

inductive Life where
  | intoIter (site thread length : Nat)
  | next (site thread remaining : Nat)
  | iteratorDrop (site thread remaining : Nat)
  | closureDrop (thread : Nat)
  | scopeDrop

structure Runtime (S : Type) where
  methods : PV_V263_MapSpine.Runtime S
  life : Life → Q S Unit
  capacityOverflow : {A : Type} → Q S A

local instance {S : Type} : Monad (Q S) where
  pure a := PV_V263_World.lift (.ok a)
  bind := PV_V263_World.bind

/-- Logical value primitive. A method overflow is routed to the native panic
handler; no synthetic source .fail is manufactured for an allocation fault. -/
def value {S A : Type} (runtime : Runtime S) (result : Result A) : Q S A :=
  match result with
  | .ok a => lift (.ok a)
  | .fail _ => runtime.capacityOverflow
  | .div => lift .div

def push {S A : Type} (runtime : Runtime S) (layouts : Layouts)
    (site thread : Nat) (out : alloc.vec.Vec A) (a : A) : Q S (alloc.vec.Vec A) := do
  runtime.methods.vector (.push site thread out.length layouts.item)
  value runtime (alloc.vec.Vec.push out a)

/-- Both mutable owners returned. The donor is empty before its destructor;
its allocation is released only by the subsequent method drop. -/
def append {S A : Type} (runtime : Runtime S) (layouts : Layouts) (site thread : Nat)
    (out source : alloc.vec.Vec A) : Q S (alloc.vec.Vec A × alloc.vec.Vec A) := do
  runtime.methods.vector (.append site thread out.length source.length layouts.item)
  if bound : out.length + source.length ≤ Usize.max then
    pure (⟨out.val ++ source.val,by simpa only [List.length_append] using bound⟩,
      alloc.vec.Vec.new A)
  else runtime.capacityOverflow

/-- TrustedLen collect stores directly after each callback; it is not the
source's push-method loop. Capacity precedes the first callback. -/
def collectLoop {S A : Type} (runtime : Runtime S) (f : Nat → Q S A) :
    List Nat → alloc.vec.Vec A → Q S (alloc.vec.Vec A)
  | [],out => pure out
  | i::ids,out => do
      let a ← f i
      let out' ← value runtime (alloc.vec.Vec.push out a)
      collectLoop runtime f ids out'

def collect {S A : Type} (runtime : Runtime S) (layouts : Layouts)
    (site thread : Nat) (ids : List Nat) (f : Nat → Q S A) : Q S (alloc.vec.Vec A) := do
  runtime.methods.vector (.collect site thread ids.length layouts.family)
  collectLoop runtime f ids (alloc.vec.Vec.new A)

abbrev Family (A : Type) := alloc.vec.Vec A × Nat
abbrev Families (A : Type) := alloc.vec.Vec (Family A)
abbrev Caught (A : Type) := Except Bytes (Families A)
abbrev Task (S A : Type) := PV_V263_DeferredJoin.Task S (Families A)

def items {S A : Type} (runtime : Runtime S) (layouts : Layouts) (n : Usize)
    (k : Nat) (callback : Nat → Q S A) : Q S (Family A) :=
  PV_V263_VectorLoop.run runtime.methods layouts n k callback

def family {S A : Type} (runtime : Runtime S) (layouts : Layouts) (n : Usize)
    (k : Nat) (callback : Nat → Q S A) : Q S (Families A) :=
  collect runtime layouts 1 k [k] (fun j => items runtime layouts n j callback)

def caughtFamily {S A : Type} (runtime : Runtime S) (layouts : Layouts) (n : Usize)
    (k : Nat) (callback : Nat → Q S A) : Q S (Caught A) :=
  withActive runtime.methods.os .abort k
    (catchPanic .abort (family runtime layouts n k callback))

def forks {S A : Type} (runtime : Runtime S) (layouts : Layouts) (n : Usize)
    (callback : Nat → Q S A) : List Nat → alloc.vec.Vec (Task S A) → Q S (alloc.vec.Vec (Task S A))
  | [],handles => pure handles
  | k::ks,handles => do
      let task ← PV_V263_DeferredJoin.fork runtime.methods.os k
        (caughtFamily runtime layouts n k callback)
      runtime.methods.vector (.push 2 0 handles.length layouts.handle)
      let handles' ← value runtime (alloc.vec.Vec.push handles task)
      forks runtime layouts n callback ks handles'

def joins {S A : Type} (runtime : Runtime S) (layouts : Layouts) :
    List (Task S A) → alloc.vec.Vec (Caught A) → Q S (alloc.vec.Vec (Caught A))
  | [],chunks => do
      runtime.life (.next 2 0 0)
      runtime.life (.iteratorDrop 2 0 0)
      runtime.methods.vector (.drop 2 0 layouts.handle)
      pure chunks
  | task::rest,chunks => do
      runtime.life (.next 2 0 (rest.length+1))
      let caught ← PV_V263_DeferredJoin.join runtime.methods.os task
      runtime.methods.vector (.push 3 0 chunks.length layouts.caught)
      let chunks' ← value runtime (alloc.vec.Vec.push chunks caught)
      joins runtime layouts rest chunks'

def merge {S A : Type} (runtime : Runtime S) (layouts : Layouts) :
    List (Caught A) → Families A → Q S (Families A)
  | [],out => do
      runtime.life (.next 3 0 0)
      runtime.life (.iteratorDrop 3 0 0)
      runtime.methods.vector (.drop 3 0 layouts.caught)
      pure out
  | caught::rest,out => do
      runtime.life (.next 3 0 (rest.length+1))
      match caught with
      | .error p => fun w => ⟨.fault (.abort p),w,[]⟩
      | .ok source => do
          let (out',_drained) ← append runtime {layouts with item := layouts.family} 4 0 out source
          runtime.methods.vector (.drop 1 out.length layouts.family)
          merge runtime layouts rest out'

def pool {S A : Type} (runtime : Runtime S) (layouts : Layouts) (n : Usize)
    (callback : Nat → Q S A) : Q S (Families A) := do
  let active ← runtime.methods.os.answer (.tlsRead 0)
  if active then
    collect runtime layouts 4 0 (List.range 16) (fun k => items runtime layouts n k callback)
  else
    withActive runtime.methods.os .abort 0 (do
      runtime.methods.vector (.empty 2 0 layouts.handle)
      let handles ← forks runtime layouts n callback (List.range' 1 15) (alloc.vec.Vec.new _)
      let first ← caughtFamily runtime layouts n 0 callback
      runtime.methods.vector (.capacity 3 0 16 layouts.caught)
      runtime.methods.vector (.push 3 0 0 layouts.caught)
      let chunks ← value runtime (alloc.vec.Vec.push (alloc.vec.Vec.new _) first)
      runtime.life (.intoIter 2 0 handles.length)
      let caught ← joins runtime layouts handles.val chunks
      runtime.methods.os.answer (.cleanup 0)
      runtime.life .scopeDrop
      runtime.methods.vector (.capacity 4 0 16 layouts.family)
      runtime.life (.intoIter 3 0 caught.length)
      let out ← merge runtime layouts caught.val (alloc.vec.Vec.new _)
      runtime.life (.closureDrop 0)
      pure out)

def appendItems {S A : Type} (runtime : Runtime S) (layouts : Layouts) :
    List (Family A) → Nat → alloc.vec.Vec A → Q S (alloc.vec.Vec A)
  | [],_,out => do
      runtime.life (.next 4 0 0)
      runtime.life (.iteratorDrop 4 0 0)
      runtime.methods.vector (.drop 4 0 layouts.family)
      pure out
  | (source,_completed)::rest,k,out => do
      runtime.life (.next 4 0 (rest.length+1))
      let (out',_drained) ← append runtime layouts 5 0 out source
      runtime.methods.vector (.drop 0 k layouts.item)
      appendItems runtime layouts rest (k+1) out'

def run {S A : Type} (runtime : Runtime S) (layouts : Layouts)
    (_stage n : Usize) (callback : Nat → Q S A) : Q S (alloc.vec.Vec A) := do
  let chunks ← pool runtime layouts n callback
  runtime.methods.vector (.capacity 5 0 n.val layouts.item)
  runtime.life (.intoIter 4 0 chunks.length)
  let out ← appendItems runtime layouts chunks.val 0 (alloc.vec.Vec.new _)
  runtime.life (.closureDrop 0)
  pure out

/-- A failed append-method effect retains its precise post-world. -/
theorem append_fault {S A : Type} (runtime : Runtime S) (layouts : Layouts)
    (site thread : Nat) (out source : alloc.vec.Vec A) (w : State S) (e : Fault)
    (h : (runtime.methods.vector (.append site thread out.length source.length layouts.item) w).outcome = .fault e) :
    (append runtime layouts site thread out source w).outcome = .fault e := by
  change (PV_V263_World.bind
    (runtime.methods.vector (.append site thread out.length source.length layouts.item)) _ w).outcome = _
  simp only [PV_V263_World.bind,h]

#print axioms Life
#print axioms Runtime
#print axioms value
#print axioms push
#print axioms append
#print axioms collectLoop
#print axioms collect
#print axioms items
#print axioms family
#print axioms caughtFamily
#print axioms forks
#print axioms joins
#print axioms merge
#print axioms pool
#print axioms appendItems
#print axioms run
#print axioms append_fault
end R1Z.PV_V263_VecSpine
