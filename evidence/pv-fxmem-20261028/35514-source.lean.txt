import Aeneas
set_option autoImplicit false
namespace R1Z.PV_FXM_ReserveWorld
open Aeneas Aeneas.Std

/-- Total encoding; on admitted target-size layouts this is exact. -/
def usize (n : Nat) : Usize :=
  Usize.ofNatCore (n % (Usize.max+1))
    (Nat.le_of_lt_succ (Nat.mod_lt n (Nat.zero_lt_succ Usize.max)))

theorem usize_exact (n : Nat) (h : n≤Usize.max) : (usize n).val=n := by
  change n % (Usize.max+1)=n
  exact Nat.mod_eq_of_lt (Nat.lt_succ_of_le h)

inductive Error where
  | capacityOverflow
  | allocError (layout : core.alloc.layout.Layout)

structure Shape where
  width : Nat
  align : core.ptr.alignment.Alignment

structure Buffer (T : Type) where
  address : Nat
  capacity : Nat
  values : List T
  fits : values.length ≤ capacity

structure Request where
  address : Nat
  oldCapacity : Nat
  newCapacity : Nat
  shape : Shape

structure Event where
  request : Request
  returnedAddress : Option Nat

structure World (S F : Type) where
  allocator : S
  allocCalls : Nat
  reallocCalls : Nat
  deallocCalls : Nat
  successfulAlloc : Nat
  successfulRealloc : Nat
  drops : Nat
  history : List Event
  memory : Nat → Option Nat
  live : Nat → Bool
  frame : F

structure Execution (T S F : Type) where
  returned : Except Error Unit
  buffer : Buffer T
  world : World S F

/-- Standard raw allocation/reallocation memory interpretation: growth copies
all old allocation bytes, including uninitialized slots, from a snapshot; new
spare bytes remain uninitialized. Freed old storage is not asserted zero. -/
def memoryAfter (r : Request) (p : Nat) (memory : Nat → Option Nat) : Nat → Option Nat :=
  fun a => if p≤a ∧ a<p+r.newCapacity*r.shape.width then
    if a-p<r.oldCapacity*r.shape.width then memory (r.address+(a-p)) else none
  else memory a

def attempted {S F : Type} (r : Request) (p : Option Nat) (s : S)
    (w : World S F) : World S F :=
  {w with allocator := s
          allocCalls := w.allocCalls + if r.oldCapacity=0 then 1 else 0
          reallocCalls := w.reallocCalls + if r.oldCapacity=0 then 0 else 1
          history := w.history ++ [⟨r,p⟩]}

def succeeded {S F : Type} (r : Request) (p : Nat) (w : World S F) : World S F :=
  {w with successfulAlloc := w.successfulAlloc + if r.oldCapacity=0 then 1 else 0
          successfulRealloc := w.successfulRealloc + if r.oldCapacity=0 then 0 else 1
          memory := memoryAfter r p w.memory
          live := fun a => if a=p then true else
            if r.oldCapacity≠0 ∧ a=r.address then false else w.live a}

def finish {T S F : Type} (step : Request → S → Option Nat × S)
    (shape : Shape) (b : Buffer T) (additional : Nat) (w : World S F) : Execution T S F :=
  let cap := b.values.length+additional
  let req : Request := ⟨b.address,b.capacity,cap,shape⟩
  let (p,s) := step req w.allocator
  let w' := attempted req p s w
  match p with
  | none => ⟨.error (.allocError ⟨usize (cap*shape.width),shape.align⟩),b,w'⟩
  | some address => ⟨.ok (),⟨address,cap,b.values,Nat.le_add_right _ _⟩,succeeded req address w'⟩

/-- RawVec grow_exact: the guards precede the allocator call. `wordMax` and
`byteMax` are usize::MAX and isize::MAX for the target ABI. -/
def growExact {T S F : Type} (step : Request → S → Option Nat × S)
    (wordMax byteMax : Nat) (shape : Shape) (b : Buffer T)
    (additional : Nat) (w : World S F) : Execution T S F :=
  if shape.width=0 then ⟨.error .capacityOverflow,b,w⟩ else
  if b.values.length+additional>wordMax then ⟨.error .capacityOverflow,b,w⟩ else
  if (b.values.length+additional)*shape.width>byteMax then ⟨.error .capacityOverflow,b,w⟩ else
  finish step shape b additional w

def native {T S F : Type} (step : Request → S → Option Nat × S)
    (wordMax byteMax : Nat) (shape : Shape) (b : Buffer T)
    (additional : Nat) (w : World S F) : Execution T S F :=
  if additional>b.capacity-b.values.length then
    growExact step wordMax byteMax shape b additional w
  else ⟨.ok (),b,w⟩

/-- Owned reference tests available capacity first; the remaining cases are
exactly the source's zero-size, checked-add and layout-overflow branches. -/
def reference {T S F : Type} (step : Request → S → Option Nat × S)
    (wordMax byteMax : Nat) (shape : Shape) (b : Buffer T)
    (additional : Nat) (w : World S F) : Execution T S F :=
  if additional≤b.capacity-b.values.length then ⟨.ok (),b,w⟩ else
  if shape.width=0 ∨ b.values.length+additional>wordMax ∨
      (b.values.length+additional)*shape.width>byteMax then
    ⟨.error .capacityOverflow,b,w⟩
  else finish step shape b additional w

theorem source_reference {T S F : Type} (step : Request → S → Option Nat × S)
    (wordMax byteMax : Nat) (shape : Shape) (b : Buffer T)
    (additional : Nat) (w : World S F) :
    native step wordMax byteMax shape b additional w =
      reference step wordMax byteMax shape b additional w := by
  unfold native reference growExact
  by_cases h : additional>b.capacity-b.values.length
  · have hn : ¬ additional≤b.capacity-b.values.length := by omega
    simp only [h,hn,ite_true,ite_false]
    by_cases hz : shape.width=0 <;>
      by_cases ha : b.values.length+additional>wordMax <;>
      by_cases hl : (b.values.length+additional)*shape.width>byteMax <;>
      simp only [hz,ha,hl,or_true,true_or,or_false,false_or,ite_true,ite_false]
  · have hn : additional≤b.capacity-b.values.length := by omega
    simp only [h,hn,ite_true,ite_false]

theorem values_preserved {T S F : Type} (step : Request → S → Option Nat × S)
    (wordMax byteMax : Nat) (shape : Shape) (b : Buffer T)
    (additional : Nat) (w : World S F) :
    (native step wordMax byteMax shape b additional w).buffer.values=b.values := by
  unfold native growExact finish
  split <;> try rfl
  split <;> try rfl
  split <;> try rfl
  split <;> try rfl
  split <;> rfl

theorem no_growth {T S F : Type} (step : Request → S → Option Nat × S)
    (wordMax byteMax : Nat) (shape : Shape) (b : Buffer T)
    (additional : Nat) (w : World S F) (h : additional≤b.capacity-b.values.length) :
    native step wordMax byteMax shape b additional w=⟨.ok (),b,w⟩ := by
  simp only [native,Nat.not_lt.mpr h,ite_false]

theorem allocation_error {T S F : Type} (step : Request → S → Option Nat × S)
    (shape : Shape) (b : Buffer T) (additional : Nat) (w : World S F)
    (s : S) (h : step ⟨b.address,b.capacity,b.values.length+additional,shape⟩ w.allocator=(none,s)) :
    (finish step shape b additional w).returned =
        .error (.allocError ⟨usize ((b.values.length+additional)*shape.width),shape.align⟩) ∧
    (finish step shape b additional w).buffer=b ∧
    (finish step shape b additional w).world.allocator=s ∧
    (finish step shape b additional w).world.memory=w.memory ∧
    (finish step shape b additional w).world.live=w.live := by
  simp [finish,h,attempted]

theorem success_capacity {T S F : Type} (step : Request → S → Option Nat × S)
    (shape : Shape) (b : Buffer T) (additional : Nat) (w : World S F)
    (p : Nat) (s : S)
    (h : step ⟨b.address,b.capacity,b.values.length+additional,shape⟩ w.allocator=(some p,s)) :
    (finish step shape b additional w).returned=.ok () ∧
    (finish step shape b additional w).buffer.capacity=b.values.length+additional ∧
    (finish step shape b additional w).buffer.address=p := by
  simp [finish,h]

theorem caller_composition {T S F A : Type} (step : Request → S → Option Nat × S)
    (wordMax byteMax : Nat) (shape : Shape) (b : Buffer T)
    (additional : Nat) (w : World S F) (caller : Execution T S F → A) :
    caller (native step wordMax byteMax shape b additional w)=
      caller (reference step wordMax byteMax shape b additional w) :=
  congrArg caller (source_reference step wordMax byteMax shape b additional w)

#print axioms usize_exact
#print axioms source_reference
#print axioms values_preserved
#print axioms no_growth
#print axioms allocation_error
#print axioms success_capacity
#print axioms caller_composition
end R1Z.PV_FXM_ReserveWorld
