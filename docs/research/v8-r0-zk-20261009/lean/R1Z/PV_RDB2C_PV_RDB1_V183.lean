import R1Z.PV_RDB2C_PV_RDB1_Layout
import R1Z.PV_RDB2C_PV_RDB1_PointerConstruct

set_option autoImplicit false
namespace R1Z.PV_RDB1_V183_ReserveWorld
open Aeneas Aeneas.Std

/-- Total encoding; on admitted target-size layouts this is exact. -/
def usize (n : Nat) : Usize :=
  Usize.ofNatCore (n % (2 ^ UScalarTy.Usize.numBits))
    (Nat.mod_lt n (by positivity))

theorem usize_exact (n : Nat) (h : n<2^UScalarTy.Usize.numBits) : (usize n).val=n := by
  change n % (2^UScalarTy.Usize.numBits)=n
  exact Nat.mod_eq_of_lt h

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
  dsimp only
  cases step ⟨b.address,b.capacity,b.values.length+additional,shape⟩ w.allocator with
  | mk p s => cases p <;> rfl

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
end R1Z.PV_RDB1_V183_ReserveWorld

set_option autoImplicit false
namespace R1Z.PV_RDB1_V183_ReserveLayout
open Aeneas Aeneas.Std

/-- A native element layout is padded to alignment. For a power-of-two
alignment dividing isize::MAX+1, the source's rounded layout guard is exactly
the byte-limit guard in ReserveWorld. No rounding is silently omitted. -/
theorem aligned_limit (bytes limit align k m : Nat) (positive : 0<align)
    (padded : bytes=k*align) (target : limit+1=m*align) :
    bytes≤limit ↔ bytes≤limit+1-align := by
  constructor
  · intro h
    have hm : k*align<m*align := by omega
    have hk : k<m := by
      by_contra hn
      have hmk : m≤k := by omega
      have hp : m*align≤k*align := Nat.mul_le_mul_right align hmk
      omega
    have hkm : (k+1)*align≤m*align := Nat.mul_le_mul_right align hk
    rw [Nat.add_mul,Nat.one_mul] at hkm
    omega
  · intro h
    have hm : 0<m := by
      by_contra hn
      have : m=0 := by omega
      simp only [this,Nat.zero_mul] at target
      omega
    have ha : align≤m*align := by
      simpa only [Nat.one_mul] using Nat.mul_le_mul_right align hm
    omega

theorem same_alignment (size1 size2 : Usize) (align : core.ptr.alignment.Alignment) :
    (core.alloc.layout.Layout.mk size1 align).align=
      (core.alloc.layout.Layout.mk size2 align).align := rfl

theorem product_error (product wordMax byteBound : Nat) (h : byteBound≤wordMax) :
    (product>wordMax ∨ product>byteBound) ↔ product>byteBound := by omega

theorem wrapped_available (capacity len size : Nat)
    (fits : len≤capacity) (bounded : capacity<size) :
    (capacity+size-len)%size=capacity-len := by
  have h : capacity+size-len=(capacity-len)+size := by omega
  rw [h,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]

#print axioms product_error
#print axioms wrapped_available
#print axioms aligned_limit
#print axioms same_alignment
end R1Z.PV_RDB1_V183_ReserveLayout

set_option autoImplicit false
namespace R1Z.PV_RDB1_V183_ReserveFacts
open PV_RDB1_V183_ReserveWorld

theorem finish_effects {T S F : Type} (step : Request → S → Option Nat × S)
    (shape : Shape) (b : Buffer T) (additional : Nat) (w : World S F) :
    let req : Request := ⟨b.address,b.capacity,b.values.length+additional,shape⟩
    let e := finish step shape b additional w
    e.world.allocator=(step req w.allocator).2 ∧
    e.world.allocCalls=w.allocCalls+(if b.capacity=0 then 1 else 0) ∧
    e.world.reallocCalls=w.reallocCalls+(if b.capacity=0 then 0 else 1) ∧
    e.world.deallocCalls=w.deallocCalls ∧ e.world.drops=w.drops ∧
    e.world.frame=w.frame ∧ e.world.history=w.history++[⟨req,(step req w.allocator).1⟩] := by
  dsimp only
  cases h : step ⟨b.address,b.capacity,b.values.length+additional,shape⟩ w.allocator with
  | mk p s => cases p <;> simp [finish,h,attempted,succeeded]

theorem overflow_world {T S F : Type} (step : Request → S → Option Nat × S)
    (wordMax byteMax : Nat) (shape : Shape) (b : Buffer T)
    (additional : Nat) (w : World S F)
    (h : shape.width=0 ∨ b.values.length+additional>wordMax ∨
      (b.values.length+additional)*shape.width>byteMax) :
    growExact step wordMax byteMax shape b additional w=⟨.error .capacityOverflow,b,w⟩ := by
  unfold growExact
  rcases h with h|h|h
  · simp only [h,ite_true]
  · by_cases hz : shape.width=0 <;> simp only [hz,h,ite_true,ite_false]
  · by_cases hz : shape.width=0 <;>
      by_cases ha : b.values.length+additional>wordMax <;>
      simp only [hz,ha,h,ite_true,ite_false]

theorem copied_prefix (r : Request) (memory : Nat → Option Nat) (p i : Nat)
    (grow : r.oldCapacity≤r.newCapacity) (h : i<r.oldCapacity*r.shape.width) :
    memoryAfter r p memory (p+i)=memory (r.address+i) := by
  have hi : i < r.newCapacity * r.shape.width :=
    lt_of_lt_of_le h (Nat.mul_le_mul_right r.shape.width grow)
  have hp : p≤p+i := Nat.le_add_right _ _
  have hn : p+i<p+r.newCapacity*r.shape.width := Nat.add_lt_add_left hi p
  simp [memoryAfter,hp,hn,h]

theorem outside_memory (r : Request) (memory : Nat → Option Nat) (p a : Nat)
    (h : a<p ∨ p+r.newCapacity*r.shape.width≤a) :
    memoryAfter r p memory a=memory a := by
  have hn : ¬ (p≤a ∧ a<p+r.newCapacity*r.shape.width) := by omega
  simp only [memoryAfter,hn,ite_false]

theorem new_spare_uninitialized (r : Request) (memory : Nat → Option Nat) (p i : Nat)
    (h : r.oldCapacity * r.shape.width ≤ i) (hi : i < r.newCapacity * r.shape.width) :
    memoryAfter r p memory (p+i)=none := by
  have hp : p≤p+i := Nat.le_add_right _ _
  have hn : p+i<p+r.newCapacity*r.shape.width := Nat.add_lt_add_left hi p
  simp [memoryAfter,hp,hn,Nat.not_lt.mpr h]

theorem buffer_nonvacuous {T : Type} (xs : List T) (address spare : Nat) :
    ∃ b : Buffer T, b.values=xs ∧ b.address=address ∧ b.capacity=xs.length+spare :=
  ⟨⟨address,xs.length+spare,xs,Nat.le_add_right _ _⟩,rfl,rfl,rfl⟩

#print axioms finish_effects
#print axioms overflow_world
#print axioms copied_prefix
#print axioms outside_memory
#print axioms new_spare_uninitialized
#print axioms buffer_nonvacuous
end R1Z.PV_RDB1_V183_ReserveFacts

set_option autoImplicit false
namespace R1Z.PV_RDB1_V183_ReservePrimitive
open Aeneas Aeneas.Std PV_RDB1_V183_ReserveWorld

def layout (shape : Shape) (capacity : Nat) : core.alloc.layout.Layout :=
  ⟨usize (capacity*shape.width),shape.align⟩

/-- Exactly the Global runtime primitive signatures. A fresh allocation does
not receive the dangling old pointer or element count; same-align growth is
raw realloc with the old layout and requested new size. -/
def step {S : Type}
    (allocate : core.alloc.layout.Layout → S → Option Nat × S)
    (reallocate : Nat → core.alloc.layout.Layout → Usize → S → Option Nat × S)
    (r : Request) (s : S) : Option Nat × S :=
  if r.oldCapacity=0 then allocate (layout r.shape r.newCapacity) s else
    reallocate r.address (layout r.shape r.oldCapacity)
      (usize (r.newCapacity*r.shape.width)) s

theorem allocate_branch {S : Type}
    (allocate : core.alloc.layout.Layout → S → Option Nat × S)
    (reallocate : Nat → core.alloc.layout.Layout → Usize → S → Option Nat × S)
    (r : Request) (s : S) (h : r.oldCapacity=0) :
    step allocate reallocate r s=allocate (layout r.shape r.newCapacity) s := by
  simp only [step,h,ite_true]

theorem allocate_address_irrelevant {S : Type}
    (allocate : core.alloc.layout.Layout → S → Option Nat × S)
    (reallocate : Nat → core.alloc.layout.Layout → Usize → S → Option Nat × S)
    (r : Request) (s : S) (h : r.oldCapacity=0) (address : Nat) :
    step allocate reallocate {r with address := address} s=step allocate reallocate r s := by
  simp only [step,h,ite_true]

theorem realloc_branch {S : Type}
    (allocate : core.alloc.layout.Layout → S → Option Nat × S)
    (reallocate : Nat → core.alloc.layout.Layout → Usize → S → Option Nat × S)
    (r : Request) (s : S) (h : r.oldCapacity≠0) :
    step allocate reallocate r s=reallocate r.address (layout r.shape r.oldCapacity)
      (usize (r.newCapacity*r.shape.width)) s := by
  simp only [step,h,ite_false]

theorem exact_size (shape : Shape) (capacity : Nat)
    (h : capacity*shape.width<2^UScalarTy.Usize.numBits) :
    (layout shape capacity).size.val=capacity*shape.width := usize_exact _ h

theorem alignment (shape : Shape) (oldCap newCap : Nat) :
    (layout shape oldCap).align=(layout shape newCap).align := rfl

#print axioms allocate_branch
#print axioms allocate_address_irrelevant
#print axioms realloc_branch
#print axioms exact_size
#print axioms alignment
end R1Z.PV_RDB1_V183_ReservePrimitive


namespace R1Z.PV_RDB1_V183
open Aeneas Aeneas.Std Result PV_RDB1_V183_ReserveWorld

/-- Deployed repeat maps away the returned stride. Actual Rust element
layouts have power-of-two alignment and size a multiple of it; pad_element
proves the exact machine mask leaves such a layout unchanged. -/
theorem element_repeat_complete (wordBits alignBits k wordMax byteMax n : Nat)
    (representable : 2^alignBits*k < 2^wordBits) :
    (match PV_RDB1_Layout.packed wordMax byteMax
        (PV_RDB1_Layout.pad wordBits ⟨2^alignBits*k,2^alignBits⟩) n with
     | .error e => Except.error e
     | .ok repeated => Except.ok (repeated,
         (PV_RDB1_Layout.pad wordBits ⟨2^alignBits*k,2^alignBits⟩).size)).map Prod.fst =
      PV_RDB1_Layout.packed wordMax byteMax ⟨2^alignBits*k,2^alignBits⟩ n :=
  PV_RDB1_Layout.repeat_complete wordMax byteMax n _ _
    (PV_RDB1_Layout.pad_element wordBits alignBits k representable)

/-- Same full Result/effect carrier as the consumed reserve law, including
capacityOverflow, allocation error payload and allocator private state. -/
theorem complete {T S F : Type} (step : Request → S → Option Nat × S)
    (wordMax byteMax : Nat) (shape : Shape) (b : Buffer T)
    (additional : Nat) (w : World S F) :
    native step wordMax byteMax shape b additional w =
      reference step wordMax byteMax shape b additional w :=
  source_reference step wordMax byteMax shape b additional w

structure Runtime (S F : Type) where
  allocator : S
  bytes : Nat → Option Nat
  external : F

/-- Allocator-accessible bytes and external observations are retained inside
its arbitrary private state, on success AND null return. Logical allocation
snapshots do not assert preservation of freed physical memory. -/
theorem physical_effect {T S F D : Type}
    (step : Request → Runtime S F → Option Nat × Runtime S F)
    (shape : Shape) (b : Buffer T) (additional : Nat) (w : World (Runtime S F) D) :
    let req : Request := ⟨b.address,b.capacity,b.values.length+additional,shape⟩
    (finish step shape b additional w).world.allocator.bytes = (step req w.allocator).2.bytes ∧
    (finish step shape b additional w).world.allocator.external = (step req w.allocator).2.external := by
  have h := PV_RDB1_V183_ReserveFacts.finish_effects step shape b additional w
  exact ⟨congrArg Runtime.bytes h.1,congrArg Runtime.external h.1⟩

#print axioms element_repeat_complete
#print axioms complete
#print axioms physical_effect
end R1Z.PV_RDB1_V183
