import R1Z.PV_V263_RetainedSpine
/-! Pinned SetLenOnDrop store order: local_len advances at each raw write;
the borrowed Vec length is published only when the guard is dropped. On the
selected abort profile no unwind destructor is invented. These private store
states do not themselves interpret allocation or native panic diagnostics. -/
set_option autoImplicit false
namespace R1Z.PV_V263_TrustedStores
open Aeneas Aeneas.Std PV_V263_World PV_V263_VectorDrain PV_V263_BufferLoop

structure Frame (A : Type) where
  initialized : Buffer A
  published : Nat
  before : published ≤ initialized.values.length

def beginCollect {A : Type} (out : Buffer A) : Frame A :=
  ⟨out,out.values.length,Nat.le_refl _⟩

def write {A : Type} (frame : Frame A) (a : A)
    (room : frame.initialized.values.length+1 ≤ frame.initialized.capacity) : Frame A :=
  ⟨stored frame.initialized a room,frame.published,by
    rw [stored_length]
    exact frame.before.trans (Nat.le_succ _)⟩

def publish {A : Type} (frame : Frame A) : Frame A :=
  ⟨frame.initialized,frame.initialized.values.length,Nat.le_refl _⟩

theorem write_order {A : Type} (frame : Frame A) (a : A)
    (room : frame.initialized.values.length+1 ≤ frame.initialized.capacity) :
    (write frame a room).published=frame.published ∧
    (write frame a room).initialized.values.length=frame.initialized.values.length+1 ∧
    (write frame a room).initialized.capacity=frame.initialized.capacity ∧
    frame.initialized.values.length+1 ≤ Usize.max :=
  ⟨rfl,stored_length frame.initialized a room,rfl,room.trans frame.initialized.bounded⟩

theorem drop_publishes {A : Type} (frame : Frame A) :
    (publish frame).published=frame.initialized.values.length ∧
    (publish frame).initialized=frame.initialized := ⟨rfl,rfl⟩

def loop {S A : Type} (callback : Nat → Q S A) :
    (ids : List Nat) → (frame : Frame A) →
    (room : frame.initialized.values.length+ids.length ≤ frame.initialized.capacity) → Q S (Frame A)
  | [],frame,_ => lift (.ok (publish frame))
  | i::ids,frame,room =>
    PV_V263_World.bind (callback i) fun a =>
      let next := write frame a (by simp only [List.length_cons] at room; omega)
      loop callback ids next (by
        dsimp only [next,write]
        rw [stored_length]
        simp only [stored]
        simp only [List.length_cons] at room
        omega)

/-- Complete outcome, post-world and event equality. The erasure ignores the
private publication guard; it does not turn a fault into a successful buffer. -/
theorem erasure {S A : Type} (callback : Nat → Q S A)
    (ids : List Nat) (frame : Frame A)
    (room : frame.initialized.values.length+ids.length ≤ frame.initialized.capacity) :
    mapAction (fun f : Frame A => f.initialized) (loop callback ids frame room) =
      PV_V263_RetainedSpine.collectLoop callback ids frame.initialized room := by
  induction ids generalizing frame with
  | nil => funext w; rfl
  | cons i ids ih =>
    simp only [loop,map_bind]
    congr 1
    funext a
    exact ih _ _

#print axioms Frame
#print axioms beginCollect
#print axioms write
#print axioms publish
#print axioms write_order
#print axioms drop_publishes
#print axioms loop
#print axioms erasure
end R1Z.PV_V263_TrustedStores
