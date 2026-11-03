import R1Z.PV_V263_RetainedSpine
/-! Full-run erasure of reservation-carrying push and collector stores. These
proofs do not assume a successful callback, successful vector or resource
answer. Native method/lifecycle interpretation remains a separate obligation. -/
set_option autoImplicit false
namespace R1Z.PV_V263_RetainedErase
open Aeneas Aeneas.Std PV_V263_World PV_V263_VectorDrain PV_V263_BufferLoop

theorem push {S A : Type} (runtime : PV_V263_VecSpine.Runtime S)
    (layouts : PV_V263_MapSpine.Layouts) (site thread : Nat) (out : Buffer A) (a : A)
    (bound : out.values.length+1 ≤ Usize.max) :
    mapAction (fun b : Buffer A => b.values)
      (PV_V263_RetainedMethods.push runtime layouts site thread out a) =
      PV_V263_VecSpine.push runtime layouts site thread out.values a := by
  unfold PV_V263_RetainedMethods.push PV_V263_VecSpine.push
  rw [map_bind]
  congr 1
  funext unit
  simp only [dif_pos bound]
  obtain ⟨next,hpush,hvalues⟩ := PV_RunJoin_Vector44.push out.values a bound
  rw [hpush]
  have hnext : next=⟨out.values.val++[a],by
      simpa only [List.length_append,List.length_singleton] using bound⟩ :=
    Subtype.ext hvalues
  rw [hnext]
  funext w
  rfl

theorem collect {S A : Type} (runtime : PV_V263_VecSpine.Runtime S)
    (callback : Nat → Q S A) (ids : List Nat) (out : Buffer A)
    (room : out.values.length+ids.length ≤ out.capacity) :
    mapAction (fun b : Buffer A => b.values)
      (PV_V263_RetainedSpine.collectLoop callback ids out room) =
      PV_V263_VecSpine.collectLoop runtime callback ids out.values := by
  induction ids generalizing out with
  | nil => funext w; rfl
  | cons i ids ih =>
    change mapAction (fun b : Buffer A => b.values)
      (PV_V263_World.bind (callback i) _) = PV_V263_World.bind (callback i) _
    rw [map_bind]
    congr 1
    funext a
    let next := stored out a (by simp only [List.length_cons] at room; omega)
    have remaining : next.values.length+ids.length ≤ next.capacity := by
      dsimp only [next]
      rw [stored_length]
      simp only [stored]
      simp only [List.length_cons] at room
      omega
    rw [ih next remaining]
    rw [stored_push out a (by simp only [List.length_cons] at room; omega)]
    funext w
    rfl

#print axioms push
#print axioms collect
end R1Z.PV_V263_RetainedErase
