import Std.Tactic
set_option autoImplicit false
namespace R1Z.PV_FXM_ZeroWorld
inductive Event where
  | volatileWrite (address value : Nat)
  | compilerFence
  deriving DecidableEq, Repr
structure World (F : Type) where
  memory : Nat → Nat
  writes : Nat
  fences : Nat
  history : List Event
  alloc : Nat
  realloc : Nat
  dealloc : Nat
  drops : Nat
  frame : F

def byte {F : Type} (address : Nat) (w : World F) : World F :=
  {w with memory := fun a => if a=address then 0 else w.memory a
          writes := w.writes+1
          fences := w.fences+1
          history := w.history ++ [.volatileWrite address 0,.compilerFence]}

/-- The source IterMut consumes each element once, restoring each changed
borrow. Its operational byte trace includes one write and fence per element. -/
def native {F : Type} : Nat → Nat → World F → World F
  | _,0,w => w
  | address,n+1,w => native (address+1) n (byte address w)

/-- Reference uses an explicit index, independently of a mutable iterator. -/
def indexed {F : Type} (base : Nat) : Nat → Nat → World F → World F
  | _,0,w => w
  | i,n+1,w => indexed base (i+1) n (byte (base+i) w)

theorem source_reference {F : Type} (base i n : Nat) (w : World F) :
    native (base+i) n w = indexed base i n w := by
  induction n generalizing i w with
  | zero => rfl
  | succ n ih =>
    simp only [native,indexed]
    simpa only [Nat.add_assoc] using ih (i+1) (byte (base+i) w)

theorem counts {F : Type} (address n : Nat) (w : World F) :
    (native address n w).writes=w.writes+n ∧
    (native address n w).fences=w.fences+n := by
  induction n generalizing address w with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih =>
    simp only [native]
    obtain ⟨hw,hf⟩ := ih (address+1) (byte address w)
    exact ⟨hw.trans (Nat.add_right_comm _ _ _), hf.trans (Nat.add_right_comm _ _ _)⟩

theorem frame {F : Type} (address n : Nat) (w : World F) :
    (native address n w).frame=w.frame ∧
    (native address n w).alloc=w.alloc ∧
    (native address n w).realloc=w.realloc ∧
    (native address n w).dealloc=w.dealloc ∧
    (native address n w).drops=w.drops := by
  induction n generalizing address w with
  | zero => exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  | succ n ih => exact ih (address+1) (byte address w)

theorem outside {F : Type} (address n : Nat) (w : World F) (a : Nat)
    (h : a<address ∨ address+n≤a) : (native address n w).memory a=w.memory a := by
  induction n generalizing address w with
  | zero => rfl
  | succ n ih =>
    have hne : a≠address := by omega
    have hnext : a<address+1 ∨ address+1+n≤a := by omega
    rw [native,ih _ _ hnext]
    simp only [byte,hne,ite_false]

theorem overwritten {F : Type} (address n : Nat) (w : World F) (i : Nat)
    (h : i<n) : (native address n w).memory (address+i)=0 := by
  induction n generalizing address w i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero =>
      simp only [Nat.add_zero,native]
      rw [outside (address+1) n (byte address w) address (Or.inl (by omega))]
      simp only [Nat.add_zero,byte,ite_true]
    | succ i =>
      have hh : i<n := by omega
      have eq : address+(i+1)=(address+1)+i := by omega
      rw [eq,native]
      exact ih _ _ i hh

theorem caller_composition {F A : Type} (address n : Nat) (w : World F)
    (caller : World F → A) : caller (native address n w)=caller (indexed address 0 n w) := by
  have h := source_reference address 0 n w
  simpa only [Nat.add_zero] using congrArg caller h

#print axioms source_reference
#print axioms counts
#print axioms frame
#print axioms outside
#print axioms overwritten
#print axioms caller_composition
end R1Z.PV_FXM_ZeroWorld
