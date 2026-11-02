import R1Z.PV_V263_BufferLoop
/-! Connect the capacity-carrying store to the actual INNER range/reservation
site. The proof is complete-run equality to VectorLoop, not a callback success
hypothesis, and does not lower physical allocator/drop metadata. -/
set_option autoImplicit false
namespace R1Z.PV_V263_BufferFamily
open Aeneas Aeneas.Std PV_V263_World PV_V263_VectorDrain PV_V263_BufferLoop

theorem width_bound (n : Usize) (k : Nat) (hk : k < 16) :
    PV_RunJoin_WorkRange35.width n.val k ≤ Usize.max := by
  have hb := (PV_RunJoin_WorkRange35.bounded n.val k hk).2
  have maxBound : n.val ≤ Usize.max := by
    have hn := n.hmax
    simp only [Usize.max,UScalarTy.numBits,Usize.numBits] at *
    omega
  omega

def initial {A : Type} (n : Usize) (k : Nat) (hk : k < 16) : Buffer A :=
  empty (PV_RunJoin_WorkRange35.width n.val k) (width_bound n k hk)

theorem initial_room {A : Type} (n : Usize) (k : Nat) (hk : k < 16) :
    (initial (A := A) n k hk).values.length + (PV_V263_Family.indices n.val k).length ≤
      (initial (A := A) n k hk).capacity := by
  simp only [initial,empty,alloc.vec.Vec.new,alloc.vec.Vec.length,
    PV_V263_Family.indices,List.length_range',List.length_nil,Nat.zero_add,Nat.le_refl]

def run {S A : Type} (runtime : PV_V263_MapSpine.Runtime S)
    (layouts : PV_V263_MapSpine.Layouts) (n : Usize) (k : Nat) (hk : k < 16)
    (callback : Nat → Q S A) : Q S (Buffer A × Nat) :=
  PV_V263_World.bind
    (runtime.vector (.capacity 0 k (PV_RunJoin_WorkRange35.width n.val k) layouts.item)) fun _ =>
      loop runtime layouts k callback (PV_V263_Family.indices n.val k) (initial n k hk) 0
        (initial_room n k hk)

theorem erasure {S A : Type} (runtime : PV_V263_MapSpine.Runtime S)
    (layouts : PV_V263_MapSpine.Layouts) (n : Usize) (k : Nat) (hk : k < 16)
    (callback : Nat → Q S A) :
    mapAction erase (run runtime layouts n k hk callback) =
      PV_V263_VectorLoop.run runtime layouts n k callback := by
  unfold run PV_V263_VectorLoop.run
  rw [map_bind]
  congr 1
  funext granted
  exact PV_V263_BufferLoop.erasure runtime layouts k callback
    (PV_V263_Family.indices n.val k) (initial n k hk) 0 (initial_room n k hk)

#print axioms width_bound
#print axioms initial
#print axioms initial_room
#print axioms run
#print axioms erasure
end R1Z.PV_V263_BufferFamily
