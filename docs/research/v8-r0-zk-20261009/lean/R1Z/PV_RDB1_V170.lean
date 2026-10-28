import R1Z.PV_RDB1_Pointer
set_option autoImplicit false
namespace R1Z.PV_RDB1_V170_World

/-- A consumed Vec<u32> allocation, including spare capacity. Addresses and
capacity are supplied by the runtime relation, not reconstructed from a list. -/
structure Buffer where
  address : Nat
  capacity : Nat
  words : List Nat
  fits : words.length ≤ capacity

inductive Event where
  | free (address bytes align : Nat)
  deriving DecidableEq, Repr

structure World (S F : Type) where
  allocator : S
  allocations : Nat
  reallocations : Nat
  deallocations : Nat
  elementDestructors : Nat
  history : List Event
  live : Nat → Bool
  memory : Nat → Nat
  frame : F

/-- System deallocation is an explicit operational primitive. Its private
allocator state is retained. No claim that free clears the old bytes is made. -/
def release {S F : Type} (free : Nat → Nat → Nat → S → S)
    (b : Buffer) (w : World S F) : World S F :=
  if b.capacity = 0 then w else
  { w with allocator := free b.address (4*b.capacity) 4 w.allocator
           deallocations := w.deallocations+1
           history := w.history ++ [.free b.address (4*b.capacity) 4]
           live := fun a => if a=b.address then false else w.live a }

/-- u32 slice drop has no destructor calls; RawVec then frees its allocation.
The buffer is consumed: it is not returned as an empty but still live Vec. -/
def native {S F : Type} (free : Nat → Nat → Nat → S → S)
    (b : Buffer) (w : World S F) : Unit × World S F :=
  ((), release free b w)

def reference {S F : Type} (free : Nat → Nat → Nat → S → S)
    (b : Buffer) (w : World S F) : Unit × World S F :=
  if b.capacity = 0 then ((),w) else
  ((), { w with allocator := free b.address (4*b.capacity) 4 w.allocator
                deallocations := w.deallocations+1
                history := w.history ++ [.free b.address (4*b.capacity) 4]
                live := fun a => if a=b.address then false else w.live a })

theorem source_reference {S F : Type} (free : Nat → Nat → Nat → S → S)
    (b : Buffer) (w : World S F) : native free b w = reference free b w := by
  unfold native release reference
  split <;> rfl

theorem effects {S F : Type} (free : Nat → Nat → Nat → S → S)
    (b : Buffer) (w : World S F) :
    (native free b w).2.allocations = w.allocations ∧
    (native free b w).2.reallocations = w.reallocations ∧
    (native free b w).2.elementDestructors = w.elementDestructors ∧
    (native free b w).2.memory = w.memory ∧
    (native free b w).2.frame = w.frame := by
  unfold native release
  split <;> exact ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem no_capacity {S F : Type} (free : Nat → Nat → Nat → S → S)
    (b : Buffer) (w : World S F) (h : b.capacity=0) : native free b w = ((),w) := by
  simp only [native,release,h,ite_true]

theorem allocated {S F : Type} (free : Nat → Nat → Nat → S → S)
    (b : Buffer) (w : World S F) (h : b.capacity≠0) :
    (native free b w).2.deallocations=w.deallocations+1 ∧
    (native free b w).2.history=w.history++[.free b.address (4*b.capacity) 4] ∧
    (native free b w).2.live b.address=false := by
  simp [native,release,h]

/-- The caller continues in the post-deallocation world, not the old world. -/
theorem caller_composition {S F A : Type} (free : Nat → Nat → Nat → S → S)
    (b : Buffer) (w : World S F) (caller : Unit → World S F → A) :
    caller (native free b w).1 (native free b w).2 =
      caller () (release free b w) := rfl

theorem nonvacuous (words : List Nat) (address spare : Nat) :
    ∃ b : Buffer, b.words=words ∧ b.address=address ∧
      b.capacity=words.length+spare :=
  ⟨⟨address,words.length+spare,words,Nat.le_add_right _ _⟩,rfl,rfl,rfl⟩

#print axioms source_reference
#print axioms effects
#print axioms no_capacity
#print axioms allocated
#print axioms caller_composition
#print axioms nonvacuous
end R1Z.PV_RDB1_V170_World

namespace R1Z.PV_RDB1_V170
open Aeneas Aeneas.Std Result PV_RDB1_Pointer

structure SlicePtr (T P : Type) where
  data : Ptr T P
  len : Nat

def deployedSlice {T P : Type} (p : Ptr T P) (n : Nat) : SlicePtr T P := ⟨p,n⟩
def historicalSlice {T P : Type} (p : Ptr T P) (n : Nat) : SlicePtr T P := ⟨p,n⟩

/-- Free-function and method spellings construct the same fat pointer before
calling the same drop primitive. Arbitrary Result/effects are preserved. -/
theorem slice_drop_complete {T P W : Type} (p : Ptr T P) (n : Nat) (w : W)
    (drop : SlicePtr T P → W → Result (Unit × W)) :
    drop (deployedSlice p n) w = drop (historicalSlice p n) w := rfl

/-- Both runtime deallocator wrappers call the same allocator primitive with
address, allocation byte size and alignment, for every possible Result. -/
theorem deallocator_complete {P W : Type} (p : NonNull U8 P) (size align : Nat)
    (w : W) (dealloc : Ptr U8 P → Nat → Nat → W → Result (Unit × W)) :
    dealloc (asPtr (deployedCast (U := U8) p)) size align w =
      dealloc (asPtr p) size align w := by cases p with | mk p => cases p; rfl

/-- u32 has no user destructor. Slice glue's iteration therefore has zero
user-drop events for every length, including an empty live prefix with spare
allocated capacity. It does not deallocate the backing allocation itself. -/
def scalarDrops {W : Type} : Nat → W → W
  | 0,w => w
  | n+1,w => scalarDrops n w

theorem u32_slice_drops {W : Type} (n : Nat) (w : W) : scalarDrops n w = w := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

/-- Complete Result/effect law; free's private state remains explicit, and
freed allocation identities are invalidated. The existing returning-free
boundary is retained; no byte clearing is claimed. -/
theorem complete {S F : Type} (free : Nat → Nat → Nat → S → S)
    (b : PV_RDB1_V170_World.Buffer) (w : PV_RDB1_V170_World.World S F) :
    (ok (PV_RDB1_V170_World.native free b w) :
      Result (Unit × PV_RDB1_V170_World.World S F)) =
      ok (PV_RDB1_V170_World.reference free b w) :=
  congrArg Result.ok (PV_RDB1_V170_World.source_reference free b w)

#print axioms slice_drop_complete
#print axioms deallocator_complete
#print axioms u32_slice_drops
#print axioms complete
end R1Z.PV_RDB1_V170
