import R1Z.PV_V263_RetainedMethods
/-! Entire outer source port with retained reservations. Buffers occur in every
store and in the actual delayed callback tasks. No empty donor is replaced by
an owner without its reservation. Native allocation/ownership and lifecycle
interpretation are still required before this port can bind op257. -/
set_option autoImplicit false
namespace R1Z.PV_V263_RetainedSpine
open Aeneas Aeneas.Std PV_V263_World PV_V263_VectorDrain PV_V263_WorkerControl
open PV_RJ4IDB (Bytes)
open PV_V263_RetainedMethods (Runtime Layouts)
local instance {S : Type} : Monad (Q S) where
  pure a := lift (.ok a)
  bind := PV_V263_World.bind

theorem sixteen_bound : 16 ≤ Usize.max := by
  have hn := (16#usize).hmax
  simp only [Usize.max,UScalarTy.numBits,Usize.numBits] at *
  omega

def unitBuffer {A : Type} : Buffer A := empty 0 (Nat.zero_le _)
abbrev Family (A : Type) := Buffer A × Nat
abbrev Families (A : Type) := Buffer (Family A)
abbrev Caught (A : Type) := Except Bytes (Families A)
abbrev Task (S A : Type) := PV_V263_DeferredJoin.Task S (Families A)

/-- Raw TrustedLen stores have no push-method effect. The room invariant
justifies each store and is independent of callback answers. -/
def collectLoop {S A : Type} (f : Nat → Q S A) :
    (ids : List Nat) → (out : Buffer A) →
    (room : out.values.length+ids.length ≤ out.capacity) → Q S (Buffer A)
  | [],out,_ => pure out
  | i::ids,out,room => do
      let a ← f i
      let next := PV_V263_BufferLoop.stored out a (by
        simp only [List.length_cons] at room; omega)
      collectLoop f ids next (by
        dsimp only [next]
        rw [PV_V263_BufferLoop.stored_length]
        simp only [PV_V263_BufferLoop.stored]
        simp only [List.length_cons] at room
        omega)

def collect {S A : Type} (runtime : Runtime S) (layouts : Layouts)
    (site thread : Nat) (ids : List Nat) (f : Nat → Q S A) : Q S (Buffer A) := do
  runtime.methods.vector (.collect site thread ids.length layouts.family)
  if bound : ids.length ≤ Usize.max then
    collectLoop f ids (empty ids.length bound) (by
      simp only [empty,alloc.vec.Vec.new,alloc.vec.Vec.length,List.length_nil,Nat.zero_add,Nat.le_refl])
  else runtime.capacityOverflow

def items {S A : Type} (runtime : Runtime S) (layouts : Layouts) (n : Usize)
    (k : Nat) (callback : Nat → Q S A) : Q S (Family A) :=
  if hk : k<16 then PV_V263_BufferFamily.run runtime.methods layouts n k hk callback
  else runtime.capacityOverflow

def family {S A : Type} (runtime : Runtime S) (layouts : Layouts) (n : Usize)
    (k : Nat) (callback : Nat → Q S A) : Q S (Families A) :=
  collect runtime layouts 1 k [k] (fun j => items runtime layouts n j callback)

def caughtFamily {S A : Type} (runtime : Runtime S) (layouts : Layouts) (n : Usize)
    (k : Nat) (callback : Nat → Q S A) : Q S (Caught A) :=
  withActive runtime.methods.os .abort k
    (catchPanic .abort (family runtime layouts n k callback))

def forks {S A : Type} (runtime : Runtime S) (layouts : Layouts) (n : Usize)
    (callback : Nat → Q S A) : List Nat → Buffer (Task S A) → Q S (Buffer (Task S A))
  | [],handles => pure handles
  | k::ks,handles => do
      let task ← PV_V263_DeferredJoin.fork runtime.methods.os k
        (caughtFamily runtime layouts n k callback)
      let handles' ← PV_V263_RetainedMethods.push runtime
        {layouts with item := layouts.handle} 2 0 handles task
      forks runtime layouts n callback ks handles'

def joins {S A : Type} (runtime : Runtime S) (layouts : Layouts) :
    List (Task S A) → Buffer (Caught A) → Q S (Buffer (Caught A))
  | [],chunks => do
      runtime.life (.next 2 0 0)
      runtime.life (.iteratorDrop 2 0 0)
      runtime.methods.vector (.drop 2 0 layouts.handle)
      pure chunks
  | task::rest,chunks => do
      runtime.life (.next 2 0 (rest.length+1))
      let caught ← PV_V263_DeferredJoin.join runtime.methods.os task
      let chunks' ← PV_V263_RetainedMethods.push runtime
        {layouts with item := layouts.caught} 3 0 chunks caught
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
          let (out',_drained) ← PV_V263_RetainedMethods.append runtime
            {layouts with item := layouts.family} 4 0 out source
          runtime.methods.vector (.drop 1 out.values.length layouts.family)
          merge runtime layouts rest out'

def pool {S A : Type} (runtime : Runtime S) (layouts : Layouts) (n : Usize)
    (callback : Nat → Q S A) : Q S (Families A) := do
  let active ← runtime.methods.os.answer (.tlsRead 0)
  if active then
    collect runtime layouts 4 0 (List.range 16) (fun k => items runtime layouts n k callback)
  else
    withActive runtime.methods.os .abort 0 (do
      runtime.methods.vector (.empty 2 0 layouts.handle)
      let handles ← forks runtime layouts n callback (List.range' 1 15) unitBuffer
      let first ← caughtFamily runtime layouts n 0 callback
      runtime.methods.vector (.capacity 3 0 16 layouts.caught)
      let chunks ← PV_V263_RetainedMethods.push runtime
        {layouts with item := layouts.caught} 3 0 (empty 16 sixteen_bound) first
      runtime.life (.intoIter 2 0 handles.values.length)
      let caught ← joins runtime layouts handles.values.val chunks
      runtime.methods.os.answer (.cleanup 0)
      runtime.life .scopeDrop
      runtime.methods.vector (.capacity 4 0 16 layouts.family)
      runtime.life (.intoIter 3 0 caught.values.length)
      let out ← merge runtime layouts caught.values.val (empty 16 sixteen_bound)
      runtime.life (.closureDrop 0)
      pure out)

def appendItems {S A : Type} (runtime : Runtime S) (layouts : Layouts) :
    List (Family A) → Nat → Buffer A → Q S (Buffer A)
  | [],_,out => do
      runtime.life (.next 4 0 0)
      runtime.life (.iteratorDrop 4 0 0)
      runtime.methods.vector (.drop 4 0 layouts.family)
      pure out
  | (source,_completed)::rest,k,out => do
      runtime.life (.next 4 0 (rest.length+1))
      let (out',_drained) ← PV_V263_RetainedMethods.append runtime layouts 5 0 out source
      runtime.methods.vector (.drop 0 k layouts.item)
      appendItems runtime layouts rest (k+1) out'

def run {S A : Type} (runtime : Runtime S) (layouts : Layouts)
    (_stage n : Usize) (callback : Nat → Q S A) : Q S (Buffer A) := do
  let chunks ← pool runtime layouts n callback
  runtime.methods.vector (.capacity 5 0 n.val layouts.item)
  runtime.life (.intoIter 4 0 chunks.values.length)
  if bound : n.val ≤ Usize.max then
    let out ← appendItems runtime layouts chunks.values.val 0 (empty n.val bound)
    runtime.life (.closureDrop 0)
    pure out
  else runtime.capacityOverflow

#print axioms sixteen_bound
#print axioms unitBuffer
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
end R1Z.PV_V263_RetainedSpine
