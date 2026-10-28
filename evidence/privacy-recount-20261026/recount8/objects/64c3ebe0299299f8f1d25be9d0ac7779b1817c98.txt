import R1Z.PV_RDB1_V183
import R1Z.PV_RDB1_Copy
open Aeneas Aeneas.Std Result
namespace R1Z.PV_RDB1_Append
open PV_RDB1_V183_ReserveWorld

/-- Byte Vec amortized growth: same actual cap floor and doubling rule as
RawVec on u8. No allocator outcome is replaced by unconditional success. -/
def growthCapacity (len cap additional : Nat) : Nat :=
  max 8 (max (2*cap) (len+additional))

theorem growth_fits (len cap additional : Nat) : len ≤ growthCapacity len cap additional := by
  have h := Nat.le_max_right (2*cap) (len+additional)
  have h' := Nat.le_max_right 8 (max (2*cap) (len+additional))
  unfold growthCapacity
  omega

theorem growth_required (len cap additional : Nat) :
    len+additional ≤ growthCapacity len cap additional :=
  le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)

def finishAt {S F : Type} (step : Request → S → Option Nat × S)
    (shape : Shape) (b : Buffer U8) (additional : Nat) (w : World S F) : Execution U8 S F :=
  let cap := growthCapacity b.values.length b.capacity additional
  let req : Request := ⟨b.address,b.capacity,cap,shape⟩
  let (p,s) := step req w.allocator
  let w' := attempted req p s w
  match p with
  | none => ⟨.error (.allocError ⟨usize (cap*shape.width),shape.align⟩),b,w'⟩
  | some address =>
    ⟨.ok (),⟨address,cap,b.values,growth_fits _ _ _⟩,succeeded req address w'⟩

def reserve {S F : Type} (step : Request → S → Option Nat × S)
    (wordMax byteMax : Nat) (shape : Shape) (b : Buffer U8)
    (additional : Nat) (w : World S F) : Execution U8 S F :=
  if additional ≤ b.capacity-b.values.length then ⟨.ok (),b,w⟩ else
  if b.values.length+additional > wordMax then ⟨.error .capacityOverflow,b,w⟩ else
  if growthCapacity b.values.length b.capacity additional * shape.width > byteMax then
    ⟨.error .capacityOverflow,b,w⟩ else finishAt step shape b additional w

theorem reserve_values {S F : Type} (step : Request → S → Option Nat × S)
    (wordMax byteMax : Nat) (shape : Shape) (b : Buffer U8)
    (n : Nat) (w : World S F) :
    (reserve step wordMax byteMax shape b n w).buffer.values=b.values := by
  unfold reserve finishAt
  split <;> try rfl
  split <;> try rfl
  split <;> try rfl
  dsimp only
  cases step ⟨b.address,b.capacity,growthCapacity b.values.length b.capacity n,shape⟩ w.allocator with
  | mk p s => cases p <;> rfl

theorem reserve_zero {S F : Type} (step : Request → S → Option Nat × S)
    (wordMax byteMax : Nat) (shape : Shape) (b : Buffer U8) (w : World S F) :
    reserve step wordMax byteMax shape b 0 w = ⟨.ok (),b,w⟩ := by
  simp only [reserve,Nat.zero_le,ite_true]

theorem reserve_capacity {S F : Type} (step : Request → S → Option Nat × S)
    (wordMax byteMax : Nat) (shape : Shape) (b : Buffer U8)
    (n : Nat) (w : World S F) :
    let e := reserve step wordMax byteMax shape b n w
    e.returned=.ok () → b.values.length+n ≤ e.buffer.capacity := by
  dsimp only
  unfold reserve
  split
  · intro h
    change b.values.length+n ≤ b.capacity
    have hf := b.fits
    omega
  · split
    · intro h; cases h
    · split
      · intro h; cases h
      · unfold finishAt
        dsimp only
        cases hs : step ⟨b.address,b.capacity,growthCapacity b.values.length b.capacity n,shape⟩ w.allocator with
        | mk p s =>
          cases p with
          | none => intro h; cases h
          | some address => intro _; exact growth_required _ _ _

/-- Native raw copy observes the already-reserved pointer and unchanged live
length. Its source is a nonaliasing immutable byte slice. -/
def writeTail (address oldLen : Nat) (tail : List U8)
    (memory : Nat → Option Nat) : Nat → Option Nat :=
  fun a => if address+oldLen ≤ a ∧ a < address+oldLen+tail.length then
    (tail[a-(address+oldLen)]?).map (fun byte => byte.val)
  else memory a

structure Appended (S F : Type) where
  returned : Except PV_RDB1_V183_ReserveWorld.Error Unit
  address : Nat
  capacity : Nat
  values : List U8
  world : World S F

def appendAfter {S F : Type} (e : Execution U8 S F) (tail : List U8) : Appended S F :=
  match e.returned with
  | .error err => ⟨.error err,e.buffer.address,e.buffer.capacity,e.buffer.values,e.world⟩
  | .ok () =>
    ⟨.ok (),e.buffer.address,e.buffer.capacity,e.buffer.values++tail,
      {e.world with memory := writeTail e.buffer.address e.buffer.values.length tail e.world.memory}⟩

def source {S F : Type} (step : Request → S → Option Nat × S)
    (wordMax byteMax : Nat) (shape : Shape) (b : Buffer U8) (tail : List U8)
    (w : World S F) : Appended S F :=
  let count := tail.length
  let reserved := reserve step wordMax byteMax shape b count w
  appendAfter reserved tail

def reference {S F : Type} (step : Request → S → Option Nat × S)
    (wordMax byteMax : Nat) (shape : Shape) (b : Buffer U8) (tail : List U8)
    (w : World S F) : Appended S F :=
  appendAfter (reserve step wordMax byteMax shape b tail.length w) tail

/-- Exact buffer/header/world equality, including allocator failure and
capacity overflow BEFORE the copy. Original panic/abort handler is applied
to the same error payload after this common reserve result. -/
theorem complete {S F : Type} (step : Request → S → Option Nat × S)
    (wordMax byteMax : Nat) (shape : Shape) (b : Buffer U8) (tail : List U8)
    (w : World S F) : source step wordMax byteMax shape b tail w =
      reference step wordMax byteMax shape b tail w := rfl

theorem error_no_copy {S F : Type} (e : Execution U8 S F) (tail : List U8) (err : PV_RDB1_V183_ReserveWorld.Error)
    (h : e.returned=.error err) :
    (appendAfter e tail).values=e.buffer.values ∧ (appendAfter e tail).world=e.world := by
  simp [appendAfter,h]

theorem success_values {S F : Type} (e : Execution U8 S F) (tail : List U8)
    (h : e.returned=.ok ()) :
    (appendAfter e tail).values=e.buffer.values++tail ∧
    (appendAfter e tail).address=e.buffer.address ∧
    (appendAfter e tail).capacity=e.buffer.capacity := by
  simp [appendAfter,h]

theorem memory_frame (address oldLen : Nat) (tail : List U8)
    (memory : Nat → Option Nat) (a : Nat)
    (outside : a<address+oldLen ∨ address+oldLen+tail.length≤a) :
    writeTail address oldLen tail memory a = memory a := by
  have h : ¬(address+oldLen≤a ∧ a<address+oldLen+tail.length) := by omega
  simp only [writeTail,h,ite_false]

theorem copy_bounds (len count cap : Nat) (fits : len+count≤cap) :
    len≤len+count ∧ len+count≤cap := ⟨by omega,fits⟩

theorem doubled_cap_no_wrap (cap half : Nat) (h : cap<half) : 2*cap<2*half := by omega

#print axioms growth_required
#print axioms reserve_zero
#print axioms reserve_capacity
#print axioms growth_fits
#print axioms reserve_values
#print axioms complete
#print axioms error_no_copy
#print axioms success_values
#print axioms memory_frame
#print axioms copy_bounds
#print axioms doubled_cap_no_wrap
end R1Z.PV_RDB1_Append
