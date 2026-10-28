import R1Z.PV_FXM_ReserveWorld
set_option autoImplicit false
namespace R1Z.PV_FXM_ReserveFacts
open PV_FXM_ReserveWorld

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
  have hi : i<r.newCapacity*r.shape.width :=
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
    (h : r.oldCapacity*r.shape.width≤i) (hi : i<r.newCapacity*r.shape.width) :
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
end R1Z.PV_FXM_ReserveFacts
