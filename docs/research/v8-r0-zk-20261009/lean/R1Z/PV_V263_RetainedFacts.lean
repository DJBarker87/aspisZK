import R1Z.PV_V263_RetainedSpine
import R1Z.PV_V263_OutputShape
/-! Store invariants for arbitrary worker outcomes, not callback totality.
These identify the reserved branch before native allocator interpretation. -/
set_option autoImplicit false
namespace R1Z.PV_V263_RetainedFacts
open Aeneas Aeneas.Std PV_V263_World PV_V263_VectorDrain
open PV_V263_OutputShape

theorem loop_shape {S A : Type} (runtime : PV_V263_MapSpine.Runtime S)
    (layouts : PV_V263_MapSpine.Layouts) (thread : Nat) (callback : Nat → Q S A)
    (ids : List Nat) (out : Buffer A) (completed : Nat)
    (room : out.values.length+ids.length ≤ out.capacity) :
    Post (fun (p : Buffer A × Nat) =>
      p.1.values.length=out.values.length+ids.length ∧
      p.1.capacity=out.capacity ∧ p.2=completed+ids.length)
      (PV_V263_BufferLoop.loop runtime layouts thread callback ids out completed room) := by
  induction ids generalizing out completed with
  | nil => exact pure_post _ (out,completed) ⟨by omega,rfl,by omega⟩
  | cons i ids ih =>
    apply bind_any
    intro a
    apply bind_any
    intro unit
    let next := PV_V263_BufferLoop.stored out a (by
      simp only [List.length_cons] at room; omega)
    have remaining : next.values.length+ids.length ≤ next.capacity := by
      dsimp only [next]
      rw [PV_V263_BufferLoop.stored_length]
      simp only [PV_V263_BufferLoop.stored]
      simp only [List.length_cons] at room
      omega
    have rec := ih next (completed+1) remaining
    intro w p hp
    obtain ⟨hlen,hcap,hcount⟩ := rec w p hp
    have step : next.values.length=out.values.length+1 := PV_V263_BufferLoop.stored_length _ _ _
    have cap : next.capacity=out.capacity := rfl
    simp only [List.length_cons]
    exact ⟨by omega,hcap.trans cap,by omega⟩

theorem items_shape {S A : Type} (runtime : PV_V263_MapSpine.Runtime S)
    (layouts : PV_V263_MapSpine.Layouts) (n : Usize) (k : Nat) (hk : k<16)
    (callback : Nat → Q S A) :
    Post (fun (p : Buffer A × Nat) =>
      p.1.values.length=PV_RunJoin_WorkRange35.width n.val k ∧
      p.1.capacity=PV_RunJoin_WorkRange35.width n.val k ∧
      p.2=PV_RunJoin_WorkRange35.width n.val k)
      (PV_V263_BufferFamily.run runtime layouts n k hk callback) := by
  apply bind_any
  intro unit
  simpa only [PV_V263_BufferFamily.initial,empty,alloc.vec.Vec.new,
    alloc.vec.Vec.length,List.length_nil,Nat.zero_add,
    PV_V263_Family.indices,List.length_range'] using
    loop_shape runtime layouts k callback (PV_V263_Family.indices n.val k)
      (PV_V263_BufferFamily.initial n k hk) 0 (PV_V263_BufferFamily.initial_room n k hk)

theorem collect_shape {S A : Type} (callback : Nat → Q S A)
    (ids : List Nat) (out : Buffer A)
    (room : out.values.length+ids.length ≤ out.capacity) :
    Post (fun (p : Buffer A) =>
      p.values.length=out.values.length+ids.length ∧ p.capacity=out.capacity)
      (PV_V263_RetainedSpine.collectLoop callback ids out room) := by
  induction ids generalizing out with
  | nil => exact pure_post _ out ⟨by omega,rfl⟩
  | cons i ids ih =>
    apply bind_any
    intro a
    let next := PV_V263_BufferLoop.stored out a (by
      simp only [List.length_cons] at room; omega)
    have remaining : next.values.length+ids.length ≤ next.capacity := by
      dsimp only [next]
      rw [PV_V263_BufferLoop.stored_length]
      simp only [PV_V263_BufferLoop.stored]
      simp only [List.length_cons] at room
      omega
    have rec := ih next remaining
    intro w p hp
    obtain ⟨hlen,hcap⟩ := rec w p hp
    have step : next.values.length=out.values.length+1 := PV_V263_BufferLoop.stored_length _ _ _
    have cap : next.capacity=out.capacity := rfl
    simp only [List.length_cons]
    exact ⟨by omega,hcap.trans cap⟩

/-- When the source has room, reserve establishes no larger LOWER bound:
the original reservation is retained exactly in this representation. -/
theorem reserved_capacity {A : Type} (out source : Buffer A)
    (room : out.values.length+source.values.length ≤ out.capacity) :
    max out.capacity (out.values.length+source.values.length)=out.capacity :=
  max_eq_left room

#print axioms loop_shape
#print axioms items_shape
#print axioms collect_shape
#print axioms reserved_capacity
end R1Z.PV_V263_RetainedFacts
