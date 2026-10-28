import R1Z.PV_RDB1_Pointer

open Aeneas Aeneas.Std Result
namespace R1Z.PV_RDB1_V184_VectorPopSpec
set_option autoImplicit false

/-- Pure complete-result specification. The unsupported extracted source
binding and timed-out native checks remain separate, open obligations. -/
def pop {T : Type} (v : alloc.vec.Vec T) : Option T×alloc.vec.Vec T :=
  (v.val.getLast?,⟨v.val.dropLast,by
    rw [List.length_dropLast]
    exact le_trans (Nat.sub_le _ _) v.property⟩)

def reference {T : Type} (v : alloc.vec.Vec T) : Result (Option T×alloc.vec.Vec T) :=
  ok (pop v)

theorem length {T : Type} (v : alloc.vec.Vec T) : (pop v).2.val.length=v.val.length-1 := by
  simp only [pop,List.length_dropLast]

theorem total {T : Type} (v : alloc.vec.Vec T) : ∃ p, reference v=ok p := ⟨pop v,rfl⟩
#print axioms pop
#print axioms reference
#print axioms length
#print axioms total
end R1Z.PV_RDB1_V184_VectorPopSpec

open Aeneas Aeneas.Std Result
namespace R1Z.PV_RDB1_V184_PopLast
set_option autoImplicit false

theorem last {T : Type} (xs : List T) (h : xs≠[]) :
    xs.getLast?=some (xs[xs.length-1]'(by cases xs <;> simp_all)) := by
  induction xs with
  | nil => contradiction
  | cons x xs ih =>
    cases xs with
    | nil => rfl
    | cons y ys =>
      simpa only [List.getLast?_cons_cons,List.length_cons,Nat.add_sub_cancel,
        List.getElem_cons_succ] using ih (by simp)

theorem dropLast {T : Type} (xs : List T) : xs.dropLast=xs.take (xs.length-1) := by
  exact List.dropLast_eq_take
#print axioms last
#print axioms dropLast
end R1Z.PV_RDB1_V184_PopLast

open Aeneas Aeneas.Std Result
namespace R1Z.PV_RDB1_V184_RemoveModel
set_option autoImplicit false

/-- Explicit library value semantics for native remove's read/memmove/set_len.
This declaration does not assert an Aeneas extraction of native raw pointers. -/
def remove {T : Type} (_A : Type) (v : alloc.vec.Vec T) (i : Usize) :
    Result (T × alloc.vec.Vec T) :=
  match v.val[i.val]? with
  | none => fail .panic
  | some x => ok (x,⟨v.val.take i.val ++ v.val.drop (i.val+1),by
      simp only [List.length_append,List.length_take,List.length_drop]
      have := v.property
      omega⟩)

/-- Body retained from the successful pinned borrowed extraction, with the
native remove external bound to the explicit library model above. -/
def pop_move_reference {T : Type} (v : alloc.vec.Vec T) :
    Result ((Option T) × alloc.vec.Vec T) := do
  let n := alloc.vec.Vec.len v
  if n=0#usize then ok (none,v) else
    let i ← lift (Usize.wrapping_sub n 1#usize)
    let (t,v1) ← remove Global v i
    ok (some t,v1)

#print axioms remove
#print axioms pop_move_reference
end R1Z.PV_RDB1_V184_RemoveModel

open Aeneas Aeneas.Std Result
namespace R1Z.PV_RDB1_V184_PopWorld
set_option autoImplicit false

/-- Allocation observations are retained, including pre-existing history. -/
structure World where
  alloc : Nat
  realloc : Nat
  dealloc : Nat
  history : List Nat
  deriving DecidableEq

/-- Native buffer identity and capacity are carried independently of values. -/
structure Buffer (T : Type) where
  address : Nat
  capacity : Nat
  value : alloc.vec.Vec T
  fits : value.val.length ≤ capacity

def after {T : Type} (b : Buffer T) : Buffer T :=
  ⟨b.address,b.capacity,(PV_RDB1_V184_VectorPopSpec.pop b.value).2,by
    rw [PV_RDB1_V184_VectorPopSpec.length]
    exact le_trans (Nat.sub_le _ _) b.fits⟩

def reference {T : Type} (b : Buffer T) (w : World) :
    Result (Option T × Buffer T × World) :=
  ok ((PV_RDB1_V184_VectorPopSpec.pop b.value).1,after b,w)

theorem complete {T : Type} (b : Buffer T) (w : World) :
    reference b w = ok (b.value.val.getLast?,after b,w) := rfl

theorem retains_buffer {T : Type} (b : Buffer T) :
    (after b).address=b.address ∧ (after b).capacity=b.capacity := ⟨rfl,rfl⟩

theorem remaining {T : Type} (b : Buffer T) :
    (after b).value.val=b.value.val.dropLast := rfl

theorem zero_allocations {T : Type} (b : Buffer T) (w : World) :
    ∃ r b', reference b w=ok (r,b',w) := ⟨_,_,rfl⟩

theorem nonvacuous {T : Type} (v : alloc.vec.Vec T) (address : Nat) :
    ∃ b : Buffer T, b.value=v ∧ b.address=address :=
  ⟨⟨address,v.val.length,v,le_refl _⟩,rfl,rfl⟩

#print axioms after
#print axioms reference
#print axioms complete
#print axioms retains_buffer
#print axioms remaining
#print axioms zero_allocations
#print axioms nonvacuous
end R1Z.PV_RDB1_V184_PopWorld

open Aeneas Aeneas.Std Result
namespace R1Z.PV_RDB1_V184_MoveFacts
set_option autoImplicit false

theorem sub_value (x y : Usize) (h : y.val ≤ x.val) :
    (Usize.wrapping_sub x y).val=x.val-y.val := by
  change (x.bv-y.bv).toNat=_
  exact BitVec.toNat_sub_of_le h

theorem last_value {T : Type} (v : alloc.vec.Vec T) (h : v.val ≠ []) :
    (Usize.wrapping_sub (alloc.vec.Vec.len v) 1#usize).val=v.val.length-1 := by
  have hn : 0 < v.val.length := by cases hv : v.val <;> simp_all
  exact sub_value (alloc.vec.Vec.len v) 1#usize (by change 1 ≤ v.val.length; omega)

theorem last_bound {T : Type} (v : alloc.vec.Vec T) (h : v.val ≠ []) :
    v.val.length-1 < v.val.length := by cases hv : v.val <;> simp_all

theorem zero_copy (n : Nat) (h : 0<n) : n-(n-1)-1=0 := by omega

theorem one_past (n cap : Nat) (h : 0<n) (hc : n ≤ cap) : (n-1)+1 ≤ cap := by omega

theorem empty_suffix {T : Type} (xs : List T) (h : xs ≠ []) :
    xs.drop (xs.length-1+1)=[] := by
  have hn : 0<xs.length := by cases xs <;> simp_all
  rw [show xs.length-1+1=xs.length by omega,List.drop_length]

#print axioms sub_value
#print axioms last_value
#print axioms last_bound
#print axioms zero_copy
#print axioms one_past
#print axioms empty_suffix
end R1Z.PV_RDB1_V184_MoveFacts

open Aeneas Aeneas.Std Result
namespace R1Z.PV_RDB1_V184_MoveLast
set_option autoImplicit false

theorem remove_last {T : Type} (v : alloc.vec.Vec T) (h : v.val ≠ []) :
    PV_RDB1_V184_RemoveModel.remove Global v (Usize.wrapping_sub (alloc.vec.Vec.len v) 1#usize)=
      ok (v.val[v.val.length-1]'(PV_RDB1_V184_MoveFacts.last_bound v h),
        (PV_RDB1_V184_VectorPopSpec.pop v).2) := by
  simp only [PV_RDB1_V184_RemoveModel.remove,PV_RDB1_V184_MoveFacts.last_value v h,
    List.getElem?_eq_getElem (PV_RDB1_V184_MoveFacts.last_bound v h)]
  apply congrArg Result.ok
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    simp only [PV_RDB1_V184_MoveFacts.empty_suffix v.val h,List.append_nil,
      PV_RDB1_V184_VectorPopSpec.pop,List.dropLast_eq_take]

theorem nonempty {T : Type} (v : alloc.vec.Vec T) (h : v.val ≠ []) :
    PV_RDB1_V184_RemoveModel.pop_move_reference v=
      ok (some (v.val[v.val.length-1]'(PV_RDB1_V184_MoveFacts.last_bound v h)),
        (PV_RDB1_V184_VectorPopSpec.pop v).2) := by
  have hn : alloc.vec.Vec.len v ≠ 0#usize := by
    intro hz
    have hl := congrArg (fun n : Usize => n.val) hz
    change v.val.length=0 at hl
    exact h (List.eq_nil_of_length_eq_zero hl)
  simp only [PV_RDB1_V184_RemoveModel.pop_move_reference,if_neg hn,lift,bind_tc_ok,remove_last v h]
  rfl

theorem source {T : Type} (v : alloc.vec.Vec T) :
    PV_RDB1_V184_RemoveModel.pop_move_reference v=PV_RDB1_V184_VectorPopSpec.reference v := by
  by_cases h : v.val=[]
  · have hv : v=alloc.vec.Vec.new T := Subtype.ext h
    subst v
    rfl
  · rw [nonempty v h]
    unfold PV_RDB1_V184_VectorPopSpec.reference
    apply congrArg Result.ok
    apply Prod.ext
    · exact (PV_RDB1_V184_PopLast.last v.val h).symm
    · rfl

#print axioms remove_last
#print axioms nonempty
#print axioms source
end R1Z.PV_RDB1_V184_MoveLast

open Aeneas Aeneas.Std
namespace R1Z.PV_RDB1_V184_MoveMemory
set_option autoImplicit false

/-- Data-buffer/external bytes. The vector header is carried separately. -/
abbrev Memory := Nat → Option U8

/-- Snapshot-copy semantics of the raw memmove primitive. No allocator or
payload destructor is invoked by this primitive. -/
def copyBytes (memory : Memory) (src dst count : Nat) : Memory :=
  fun i => if dst ≤ i ∧ i < dst+count then memory (src+(i-dst)) else memory i

theorem copy_zero (memory : Memory) (src dst : Nat) : copyBytes memory src dst 0=memory := by
  funext i
  simp only [copyBytes,Nat.add_zero,if_neg (by omega : ¬(dst ≤ i ∧ i<dst))]

/-- The source remove(last) byte-copy count is zero for every element width,
including non-Copy zero-sized payloads. -/
theorem last_copy (memory : Memory) (address n width : Nat) (hn : 0<n) :
    copyBytes memory (address+n*width) (address+(n-1)*width) ((n-(n-1)-1)*width)=memory := by
  rw [PV_RDB1_V184_MoveFacts.zero_copy n hn,Nat.zero_mul,copy_zero]

structure Observation (T F : Type) where
  returned : Option T
  remaining : alloc.vec.Vec T
  buffer : Nat
  capacity : Nat
  world : PV_RDB1_V184_PopWorld.World
  memory : Memory
  frame : F

#print axioms copyBytes
#print axioms copy_zero
#print axioms last_copy
end R1Z.PV_RDB1_V184_MoveMemory

open Aeneas Aeneas.Std Result
namespace R1Z.PV_RDB1_V184_MoveNativeValue
set_option autoImplicit false

/-- Initialized backing slots are separate from the live vector header. -/
def readSlot {T : Type} (backing : alloc.vec.Vec T) (i : Usize) : Result T :=
  match backing.val[i.val]? with | none => fail .undef | some x => ok x

def shorten {T : Type} (backing : alloc.vec.Vec T) (i : Usize) : alloc.vec.Vec T :=
  ⟨backing.val.take i.val,by
    rw [List.length_take]
    exact le_trans (Nat.min_le_right _ _) backing.property⟩

/-- Structural library interpretation of frozen Vec::pop: decrement the live
header, check capacity, then read the last initialized backing slot. -/
def nativeValue {T : Type} (backing : alloc.vec.Vec T) (capacity : Nat) :
    Result (Option T × alloc.vec.Vec T) := do
  let n := alloc.vec.Vec.len backing
  if n=0#usize then ok (none,backing) else
    let last := Usize.wrapping_sub n 1#usize
    let remaining := shorten backing last
    if last.val < capacity then
      let x ← readSlot backing last
      ok (some x,remaining)
    else fail .undef

theorem source {T : Type} (v : alloc.vec.Vec T) (capacity : Nat)
    (fits : v.val.length ≤ capacity) :
    nativeValue v capacity=PV_RDB1_V184_VectorPopSpec.reference v := by
  by_cases h : v.val=[]
  · have hv : v=alloc.vec.Vec.new T := Subtype.ext h
    subst v
    rfl
  · have hn : alloc.vec.Vec.len v ≠ 0#usize := by
      intro hz
      have hl := congrArg (fun n : Usize => n.val) hz
      change v.val.length=0 at hl
      exact h (List.eq_nil_of_length_eq_zero hl)
    have hi := PV_RDB1_V184_MoveFacts.last_value v h
    have hb := PV_RDB1_V184_MoveFacts.last_bound v h
    have hc : v.val.length - 1 < capacity := by omega
    simp only [nativeValue,if_neg hn,readSlot,hi,if_pos hc,List.getElem?_eq_getElem hb,bind_tc_ok,
      PV_RDB1_V184_VectorPopSpec.reference]
    apply congrArg Result.ok
    apply Prod.ext
    · exact (PV_RDB1_V184_PopLast.last v.val h).symm
    · apply Subtype.ext
      simp only [shorten,hi,PV_RDB1_V184_VectorPopSpec.pop,List.dropLast_eq_take]

theorem reference {T : Type} (v : alloc.vec.Vec T) (capacity : Nat)
    (fits : v.val.length ≤ capacity) :
    nativeValue v capacity=PV_RDB1_V184_RemoveModel.pop_move_reference v := by
  rw [source v capacity fits,PV_RDB1_V184_MoveLast.source]

#print axioms readSlot
#print axioms shorten
#print axioms nativeValue
#print axioms source
#print axioms reference
end R1Z.PV_RDB1_V184_MoveNativeValue

open Aeneas Aeneas.Std Result
namespace R1Z.PV_RDB1_V184_MoveWorld
open PV_RDB1_V184_MoveMemory
set_option autoImplicit false

def expected {T F : Type} (b : PV_RDB1_V184_PopWorld.Buffer T) (w : PV_RDB1_V184_PopWorld.World)
    (memory : Memory) (frame : F) : Observation T F :=
  ⟨(PV_RDB1_V184_VectorPopSpec.pop b.value).1,(PV_RDB1_V184_VectorPopSpec.pop b.value).2,
    b.address,b.capacity,w,memory,frame⟩

/-- Raw remove(last)'s snapshot-copy step, including size-zero elements. -/
def referenceMemory {T : Type} (b : PV_RDB1_V184_PopWorld.Buffer T) (memory : Memory)
    (width : Nat) : Memory :=
  let n := b.value.val.length
  if n=0 then memory else
    copyBytes memory (b.address+n*width) (b.address+(n-1)*width) ((n-(n-1)-1)*width)

theorem reference_memory {T : Type} (b : PV_RDB1_V184_PopWorld.Buffer T) (memory : Memory)
    (width : Nat) : referenceMemory b memory width=memory := by
  by_cases hn : b.value.val.length=0
  · simp only [referenceMemory,hn,if_true]
  · simp only [referenceMemory,hn,if_false]
    exact last_copy memory b.address _ width (by omega)

/-- The allocation world, data-buffer bytes and arbitrary external frame are
carried explicitly. Native pop has read/header effects and no allocator call. -/
def nativeWorld {T F : Type} (b : PV_RDB1_V184_PopWorld.Buffer T) (w : PV_RDB1_V184_PopWorld.World)
    (memory : Memory) (frame : F) : Result (Observation T F) := do
  let (returned,remaining) ← PV_RDB1_V184_MoveNativeValue.nativeValue b.value b.capacity
  ok ⟨returned,remaining,b.address,b.capacity,w,memory,frame⟩

/-- Safe move reference with its raw zero-length copy effect, not an assumed
world equation or an allocation-erased projection. -/
def referenceWorld {T F : Type} (b : PV_RDB1_V184_PopWorld.Buffer T) (w : PV_RDB1_V184_PopWorld.World)
    (memory : Memory) (frame : F) (width : Nat) : Result (Observation T F) := do
  let (returned,remaining) ← PV_RDB1_V184_RemoveModel.pop_move_reference b.value
  ok ⟨returned,remaining,b.address,b.capacity,w,referenceMemory b memory width,frame⟩

theorem native_complete {T F : Type} (b : PV_RDB1_V184_PopWorld.Buffer T) (w : PV_RDB1_V184_PopWorld.World)
    (memory : Memory) (frame : F) : nativeWorld b w memory frame=ok (expected b w memory frame) := by
  simp only [nativeWorld,PV_RDB1_V184_MoveNativeValue.source b.value b.capacity b.fits,
    PV_RDB1_V184_VectorPopSpec.reference,bind_tc_ok]
  rfl

theorem reference_complete {T F : Type} (b : PV_RDB1_V184_PopWorld.Buffer T) (w : PV_RDB1_V184_PopWorld.World)
    (memory : Memory) (frame : F) (width : Nat) :
    referenceWorld b w memory frame width=ok (expected b w memory frame) := by
  simp only [referenceWorld,PV_RDB1_V184_MoveLast.source,PV_RDB1_V184_VectorPopSpec.reference,bind_tc_ok,
    reference_memory b memory width]
  rfl

theorem source_reference {T F : Type} (b : PV_RDB1_V184_PopWorld.Buffer T) (w : PV_RDB1_V184_PopWorld.World)
    (memory : Memory) (frame : F) (width : Nat) :
    nativeWorld b w memory frame=referenceWorld b w memory frame width := by
  rw [native_complete,reference_complete]

theorem checked_observation {T F : Type} (b : PV_RDB1_V184_PopWorld.Buffer T) (w : PV_RDB1_V184_PopWorld.World)
    (memory : Memory) (frame : F) :
    ∃ o, nativeWorld b w memory frame=ok o ∧
      o.returned=b.value.val.getLast? ∧ o.remaining.val=b.value.val.dropLast ∧
      o.buffer=b.address ∧ o.capacity=b.capacity ∧ o.world=w ∧ o.memory=memory ∧ o.frame=frame :=
  ⟨expected b w memory frame,native_complete b w memory frame,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

#print axioms expected
#print axioms referenceMemory
#print axioms reference_memory
#print axioms nativeWorld
#print axioms referenceWorld
#print axioms native_complete
#print axioms reference_complete
#print axioms source_reference
#print axioms checked_observation
end R1Z.PV_RDB1_V184_MoveWorld


namespace R1Z.PV_RDB1_V184
open Aeneas Aeneas.Std Result
open PV_RDB1_Pointer

/-- Complete Result and world observation at the original structural library
boundary. Pointer representation has been resolved by cast_complete; the
carrier, read/header/copy and intrinsic semantics retain their original scope. -/
theorem complete {T F : Type} (b : PV_RDB1_V184_PopWorld.Buffer T)
    (w : PV_RDB1_V184_PopWorld.World) (memory : PV_RDB1_V184_MoveMemory.Memory)
    (frame : F) (width : Nat) :
    ∃ o : PV_RDB1_V184_MoveMemory.Observation T F,
      PV_RDB1_V184_MoveWorld.nativeWorld b w memory frame = ok o ∧
      PV_RDB1_V184_MoveWorld.referenceWorld b w memory frame width = ok o ∧
      o.returned = b.value.val.getLast? ∧ o.remaining.val = b.value.val.dropLast ∧
      o.buffer = b.address ∧ o.capacity = b.capacity ∧ o.world = w ∧
      o.memory = memory ∧ o.frame = frame := by
  refine ⟨PV_RDB1_V184_MoveWorld.expected b w memory frame,
    PV_RDB1_V184_MoveWorld.native_complete b w memory frame,
    PV_RDB1_V184_MoveWorld.reference_complete b w memory frame width,
    rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- Deployed casting followed by add reaches exactly the initialized slot the
retained read semantics consume, including provenance and width zero. -/
theorem read_address {T P : Type} (p : NonNull T P) (n width : Nat) :
    (offset (asPtr (deployedCast (U := T) p)) (n-1) width).address =
      p.pointer.address + (n-1)*width ∧
    (offset (asPtr (deployedCast (U := T) p)) (n-1) width).provenance =
      p.pointer.provenance := ⟨rfl,rfl⟩

#print axioms complete
#print axioms read_address
end R1Z.PV_RDB1_V184
