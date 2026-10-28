import R1Z.PV_OWN_View
set_option autoImplicit false
namespace R1Z.PV_OWN_Operations
open PV_OWN_Heap PV_OWN_Bytes PV_OWN_View PV_W_Threading
/-- The actual pre-world is retained by the enclosing Run calculus. -/
inductive Event where
 | allocate (size align : Nat)
 | reallocate (old size align : Nat)
 | deallocate (address size align : Nat)
 | destructor (kind : Nat) (token : Token)
 deriving DecidableEq
structure State (S X : Type) where
 memory : Memory
 allocator : S
 extra : X
abbrev Action (S X E A : Type) := M (State S X) Event E A
structure Request where
 size : Nat
 alignment : Nat
 deriving DecidableEq
/-- The runtime item supplies successful pointers and state; null retains state. -/
def allocate {S X E : Type} (primitive : Request → S → Outcome E (Option Nat) × S)
 (request : Request) (owner : Nat) : Action S X E (Option Token) :=
 emit (.allocate request.size request.alignment) fun w =>
  let (result,state) := primitive request w.allocator
  let after := {w with allocator := state}
  match result with
  | .fail e => (.fail e,after)
  | .div => (.div,after)
  | .ok none => (.ok none,after)
  | .ok (some p) =>
   let t := Token.mk p (w.memory.generations p+1)
   (.ok (some t),{after with memory := {w.memory with
    heap := put w.memory.heap p (some (emptyCell request.size request.alignment owner))
    generations := fun a => if a=p then t.generation else w.memory.generations a
    slots := fun s => if s=owner then some t else w.memory.slots s}})

/-- Actual primitive adequacy compares every pre-existing allocation's OWN size. -/
def AllocatorAdequate {S X E : Type}
 (primitive : Request → S → Outcome E (Option Nat) × S)
 (r : Request) (w : State S X) : Prop :=
 ∀ p s, primitive r w.allocator=(.ok (some p),s) →
 p≠0 ∧ r.alignment>0 ∧ p%r.alignment=0 ∧
 ∀ q c, w.memory.heap q=some c → c.live=true →
  q+c.size≤p ∨ p+r.size≤q

/-- A store has no alternate logical-cell map to forget updating. -/
def writeTyped {T : Type} (codec : Codec T) (t : Token) (c : Cell)
 (start : Nat) (v : T) (m : Memory) : Memory :=
 {m with heap := put m.heap t.address (some (store c start codec.width (codec.encode v)))}

def take (slot : Nat) (m : Memory) : Memory :=
 {m with slots := fun s => if s=slot then none else m.slots s}
def move (src dst : Nat) (t : Token) (c : Cell) (m : Memory) : Memory :=
 {m with heap := put m.heap t.address (some {c with owner := dst})
         slots := fun s => if s=src then none else if s=dst then some t else m.slots s}

def borrow (l : Loan) (m : Memory) : Memory := {m with loans := l::m.loans}
def endBorrow (m : Memory) : Memory := {m with loans := m.loans.tail}
def Readable (m : Memory) (slot : Nat) (t : Token) (c : Cell) : Prop :=
 Owned m slot t c ∧ ∀ l ∈ m.loans, l.token=t → l.exclusive=false

def retire (t : Token) (c : Cell) (m : Memory) : Memory :=
 {m with heap := put m.heap t.address (some {c with live := false})}

/-- Free after concrete element glue; runtime failures retain their post-state. -/
def free {S X E : Type} (primitive : Nat → Request → S → Outcome E Unit × S)
 (t : Token) (c : Cell) : Action S X E Unit :=
 emit (.deallocate t.address c.size c.alignment) fun w =>
  let (out,s) := primitive t.address ⟨c.size,c.alignment⟩ w.allocator
  (out,{w with allocator := s,memory := retire t c w.memory})

structure Vector (T : Type) where
 token : Token
 owner : Nat
 capacity : Nat
 values : List T

def VecView {T : Type} (codec : Codec T) (m : Memory) (v : Vector T) : Prop :=
 ∃ c, Owned m v.owner v.token c ∧ c.size=v.capacity*codec.width ∧
 c.alignment=codec.alignment ∧ v.values.length≤v.capacity ∧
 ∀ i x, v.values[i]?=some x → Represents codec c (i*codec.width) x

def BoxView {T : Type} (codec : Codec T) (m : Memory) (owner : Nat) (t : Token) (v : T) : Prop :=
 ∃ c, Owned m owner t c ∧ c.size=codec.width ∧ c.alignment=codec.alignment ∧ Represents codec c 0 v

def ArrayView {T : Type} (codec : Codec T) (c : Cell) (start : Nat) (values : List T) : Prop :=
 Fits c start (values.length*codec.width) ∧
 ∀ i x, values[i]?=some x → Represents codec c (start+i*codec.width) x

/-- A String relation requires UTF8 validity, separately from byte ownership. -/
def StringView (codec : Codec UInt8) (utf8 : List UInt8 → Prop) (m : Memory)
 (v : Vector UInt8) : Prop := VecView codec m v ∧ utf8 v.values

def truncate {T : Type} (n : Nat) (v : Vector T) : Vector T := {v with values := v.values.take n}
/-- No universal Drop instance: source/MIR must pick a particular program. -/
def sequence {S X E : Type} : List (Action S X E Unit) → Action S X E Unit
 | [] => lift (.ok ())
 | a::rest => bind a (fun _ => sequence rest)

def dropPod {S X E : Type} : Action S X E Unit := lift (.ok ())
def dropVecPod {S X E : Type}
 (dealloc : Nat → Request → S → Outcome E Unit × S) (t : Token) (c : Cell) : Action S X E Unit :=
 free dealloc t c

def dropString {S X E : Type}
 (dealloc : Nat → Request → S → Outcome E Unit × S) (t : Token) (c : Cell) : Action S X E Unit :=
 dropVecPod dealloc t c

def dropOwned {S X E : Type} (slot : Nat) (glue : Token → Action S X E Unit) : Action S X E Unit :=
 fun w =>
 let after := {w with memory := take slot w.memory}
 match w.memory.slots slot with
 | none => ⟨.ok (),after,[]⟩
 | some t => glue t after
end R1Z.PV_OWN_Operations
