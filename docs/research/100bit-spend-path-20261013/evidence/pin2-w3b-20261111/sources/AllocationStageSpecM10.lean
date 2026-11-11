import AbstractStageSpecM10

/-! Allocation-carrying extension of the existing abstract stage interface.
Counters compose along the executed branch, including failed executions.
These laws do not assert that an arbitrary annotation describes source
allocations. Concrete source constructors must supply that annotation. -/
set_option autoImplicit false
namespace AspisR1.AllocationStageSpecM10
open AbstractStageSpecM10

structure Allocation (W work : Nat) where
  elements : Nat
  bits : Nat
  width_law : bits ≤ W*elements
  creation_work : elements ≤ work

/-- Allocation fields belong to the same stage, with its exact work counter. -/
structure StageSpec {A B : Type} (W : Nat) (eager : A → Option B)
    (pre : A → Prop) (post : B → Prop) (budget : Nat → Nat)
    extends AbstractStageSpecM10.StageSpec eager pre post budget where
  allocation : (a : A) → Allocation W (run a).2

/-- One new fixed-width cell, charged to the bind's existing unit of work. -/
def join (W x y : Nat) (a : Allocation W x) (b : Allocation W y) :
    Allocation W (x+y+1) where
  elements := a.elements+b.elements+1
  bits := a.bits+b.bits+W
  width_law := by
    have h := Nat.add_le_add (Nat.add_le_add a.width_law b.width_law) (Nat.le_refl W)
    simpa only [Nat.mul_add,Nat.mul_one] using h
  creation_work := by have := a.creation_work; have := b.creation_work; omega

/-- Failure still creates the final option cell and retains prior allocations. -/
def finish (W x : Nat) (a : Allocation W x) : Allocation W (x+1) where
  elements := a.elements+1
  bits := a.bits+W
  width_law := by simpa only [Nat.mul_add,Nat.mul_one] using Nat.add_le_add_right a.width_law W
  creation_work := Nat.add_le_add_right a.creation_work 1

def seq {A B C : Type} {W : Nat} {f : A → Option B} {g : B → Option C}
    {I : A → Prop} {J : B → Prop} {K : C → Prop} {F G : Nat → Nat}
    (s : StageSpec W f I J F) (t : StageSpec W g J K G) :
    StageSpec W (fun a => (f a).bind g) I K (fun L => F L+G L+1) where
  toStageSpec := AbstractStageSpecM10.seq s.toStageSpec t.toStageSpec
  allocation a := by
    cases h : (s.run a).1 with
    | none =>
      have hw : ((AbstractStageSpecM10.seq s.toStageSpec t.toStageSpec).run a).2 = (s.run a).2+1 := by
        simp only [AbstractStageSpecM10.seq,PublicParserWork.bind,h]
      rw [hw]
      exact finish W _ (s.allocation a)
    | some b =>
      have hw : ((AbstractStageSpecM10.seq s.toStageSpec t.toStageSpec).run a).2 = (s.run a).2+(t.run b).2+1 := by
        simp only [AbstractStageSpecM10.seq,PublicParserWork.bind,h]
      rw [hw]
      exact join W _ _ (s.allocation a) (t.allocation b)

theorem allocation_le_work {A B : Type} {W : Nat} {f : A → Option B}
    {I : A → Prop} {J : B → Prop} {F : Nat → Nat}
    (s : StageSpec W f I J F) (a : A) :
    (s.allocation a).bits ≤ W*(s.run a).2 :=
  (s.allocation a).width_law.trans (Nat.mul_le_mul_left W (s.allocation a).creation_work)

theorem allocation_budget {A B : Type} {W : Nat} {f : A → Option B}
    {I : A → Prop} {J : B → Prop} {F : Nat → Nat}
    (s : StageSpec W f I J F) (L : Nat) (a : A) (ha : I a) :
    (s.allocation a).bits ≤ W*F L :=
  (allocation_le_work s a).trans (Nat.mul_le_mul_left W (s.work L a ha))

#print axioms allocation_le_work
#print axioms allocation_budget
end AspisR1.AllocationStageSpecM10
