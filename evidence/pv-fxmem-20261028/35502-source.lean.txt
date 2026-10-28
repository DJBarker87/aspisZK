import Init
set_option autoImplicit false
namespace R1Z.PV_FXM_DropWorld

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
  simp only [native,release,h,ite_false,ite_true]
  exact ⟨rfl,rfl,rfl⟩

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
end R1Z.PV_FXM_DropWorld
