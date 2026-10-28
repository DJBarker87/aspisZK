import R1Z.PV_W_Threading
set_option autoImplicit false
namespace R1Z.PV_W_Enriched
open PV_W_Threading

structure Allocation where
  size : Nat
  alignment : Nat
  capacity : Nat
  contents : Nat → Option UInt8
  owner : Nat
  live : Bool

/-- P interpreter data. Addresses identify shared cells, rather than putting
copies of static/atomic state into the destructor's input value. Extra retains
runtime-specific state not yet given a concrete native representation. -/
structure Process (Allocator Extra : Type) where
  statics : Nat → Option UInt8
  atomics : Nat → Nat
  heap : Nat → Option Allocation
  threadLocal : Nat → Nat → Option UInt8
  allocator : Allocator
  volatileWrites : List (Nat × UInt8)
  atomicOrder : List Nat
  fences : List Nat
  currentThread : Nat
  unwinding : Bool
  extra : Extra

structure World (Os Fs Allocator Extra : Type) where
  os : Os
  filesystem : Fs
  process : Process Allocator Extra

variable {Os Fs Allocator Extra C : Type}

/-- Replays FXM's flag/counter shape: counter 0 increments exactly once;
flag 1 determines the normal/panic result. This models the retained witness,
not a proof of generic Rust drop or native memory-model adequacy. -/
def dropWitness : M (World Os Fs Allocator Extra) (Option C) Unit Unit := fun w =>
  let p := w.process
  let p' := {p with atomics := fun a => if a = 0 then p.atomics 0 + 1 else p.atomics a}
  ⟨if p.atomics 1 = 0 then .ok () else .fail (), {w with process := p'}, [(w,none)]⟩

theorem drop_counter (w : World Os Fs Allocator Extra) :
    (dropWitness (C := C) w).world.process.atomics 0 = w.process.atomics 0 + 1 := by
  simp only [dropWitness, ↓reduceIte]

theorem drop_flag (w : World Os Fs Allocator Extra) :
    (dropWitness (C := C) w).world.process.atomics 1 = w.process.atomics 1 := by
  simp only [dropWitness, Nat.one_ne_zero, ↓reduceIte]

theorem drop_os_frame (w : World Os Fs Allocator Extra) :
    (dropWitness (C := C) w).world.os = w.os := rfl

theorem drop_result (w : World Os Fs Allocator Extra) :
    (dropWitness (C := C) w).outcome =
      if w.process.atomics 1 = 0 then .ok () else .fail () := rfl

/-- Both outcomes are representable on one carrier; no forgotten-state
factorisation premise is imposed. -/
theorem witness_representable (w : World Os Fs Allocator Extra) :
    (dropWitness (C := C) {w with process := {w.process with atomics := fun _ => 0}}).outcome = .ok () ∧
    (dropWitness (C := C) {w with process := {w.process with atomics := fun _ => 1}}).outcome = .fail () := by
  exact ⟨rfl,rfl⟩

/-- The witness changes process state, so it has an explicit internal event.
Its OS projection is silent; its full trace is never declared empty. -/
def DropStep (w : World Os Fs Allocator Extra) (tag : Option C)
    (next : World Os Fs Allocator Extra) : Prop :=
  tag = none ∧ next.os = w.os ∧ next.filesystem = w.filesystem ∧
    next.process.atomics 0 = w.process.atomics 0 + 1 ∧
    next.process.atomics 1 = w.process.atomics 1

theorem drop_valid : Valid (DropStep (C := C)) (dropWitness (C := C) :
    M (World Os Fs Allocator Extra) (Option C) Unit Unit) := by
  intro w
  exact .cons ⟨rfl,drop_os_frame w,rfl,drop_counter w,drop_flag w⟩ (.nil _)

variable {W O Tag E A : Type}

/-- Internal process steps have no OS tag. Observable events keep exactly
one OS pre-world; no process-state field is added to the trust carrier. -/
def projectTrace (project : W → O) : List (W × Option Tag) → List (O × Tag)
  | [] => []
  | (w,none)::xs => projectTrace project xs
  | (w,some c)::xs => (project w,c)::projectTrace project xs

theorem project_append (project : W → O) (xs ys : List (W × Option Tag)) :
    projectTrace project (xs ++ ys) = projectTrace project xs ++ projectTrace project ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x with | mk w c => cases c <;> simp only [List.cons_append,projectTrace,ih,List.cons_append]

/-- Silent steps must frame the OS state; otherwise deleting their tag would
forge continuity. No condition here says a native destructor is silent. -/
theorem project_threaded (project : W → O)
    (fullStep : W → Option Tag → W → Prop) (osStep : O → Tag → O → Prop)
    (silent : ∀ w n, fullStep w none n → project w = project n)
    (visible : ∀ w n c, fullStep w (some c) n → osStep (project w) c (project n))
    {w n : W} {cs : List (W × Option Tag)} (h : Threaded fullStep w cs n) :
    Threaded osStep (project w) (projectTrace project cs) (project n) := by
  induction h with
  | nil w => exact .nil _
  | @cons w mid last c cs first rest ih =>
    cases c with
    | none =>
      change Threaded osStep (project w) (projectTrace project cs) (project last)
      rw [silent w mid first]
      exact ih
    | some c => exact .cons (visible w mid c first) ih

#print axioms drop_counter
#print axioms drop_flag
#print axioms drop_os_frame
#print axioms drop_valid
#print axioms drop_result
#print axioms witness_representable
#print axioms project_append
#print axioms project_threaded
end R1Z.PV_W_Enriched
