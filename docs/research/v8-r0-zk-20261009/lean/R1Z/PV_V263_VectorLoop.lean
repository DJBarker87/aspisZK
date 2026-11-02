import R1Z.PV_V263_GrantItems
import R1Z.PV_RunJoin_Vector44
/-! Actual source Vec carrier and explicit accumulated pushes for the INNER
host_work loop. Native capacity/heap/drop lowering remains V400-257. This does
not install the outer pool or supply the actual callback-success law. -/
set_option autoImplicit false
namespace R1Z.PV_V263_VectorLoop
open Aeneas Aeneas.Std PV_V263_World PV_V263_WorkerRequests
open PV_V263_GrantControl
open PV_RJ4IDB (Bytes)

/-- Callback, vector-method effect, value store, completed increment, next item.
Both source Result constructors and native faults/exhaustion are preserved. -/
def loop {S A : Type} (runtime : PV_V263_MapSpine.Runtime S)
    (layouts : PV_V263_MapSpine.Layouts) (thread : Nat) (callback : Nat → Q S A) :
    List Nat → alloc.vec.Vec A → Nat → Q S (alloc.vec.Vec A × Nat)
  | [],out,completed => lift (.ok (out,completed))
  | i::ids,out,completed =>
      PV_V263_World.bind (callback i) fun a =>
      PV_V263_World.bind (runtime.vector (.push 0 thread out.length layouts.item)) fun _ =>
      PV_V263_World.bind (lift (alloc.vec.Vec.push out a)) fun next =>
      loop runtime layouts thread callback ids next (completed+1)

def run {S A : Type} (runtime : PV_V263_MapSpine.Runtime S)
    (layouts : PV_V263_MapSpine.Layouts) (n : Usize) (k : Nat) (callback : Nat → Q S A) :
    Q S (alloc.vec.Vec A × Nat) :=
  PV_V263_World.bind (runtime.vector (.capacity 0 k (PV_RunJoin_WorkRange35.width n.val k) layouts.item))
    fun _ => loop runtime layouts k callback (PV_V263_Family.indices n.val k)
      (alloc.vec.Vec.new A) 0

theorem granting_loop {S A : Type} (osCodec : {B : Type} → Request B → Bytes)
    (vecCodec : PV_V263_MapSpine.VecCall → Bytes) (layouts : PV_V263_MapSpine.Layouts)
    (thread : Nat) (callback : Nat → Q S A) (ids : List Nat)
    (law : ∀ i, i ∈ ids → Total (callback i)) (out : alloc.vec.Vec A) (completed : Nat)
    (room : out.length + ids.length ≤ Usize.max) (w : State S) :
    ∃ result, (loop (resourceWorld osCodec vecCodec) layouts thread callback ids out completed w).outcome =
      .returned (.ok result) ∧ result.1.length = out.length+ids.length ∧
      result.2 = completed+ids.length := by
  induction ids generalizing out completed w with
  | nil => exact ⟨(out,completed),rfl,by simp,by simp⟩
  | cons i ids ih =>
    simp only [List.length_cons] at room
    obtain ⟨a,ha,_⟩ := law i (by simp) w
    obtain ⟨next,hpush,hval⟩ := PV_RunJoin_Vector44.push out a (by omega)
    have nextLength : next.length=out.length+1 := by
      change next.val.length=out.val.length+1
      rw [hval,List.length_append,List.length_singleton]
    have nextRoom : next.length+ids.length ≤ Usize.max := by
      rw [nextLength]
      omega
    obtain ⟨result,hr,hlen,hcompleted⟩ := ih
      (fun j hj => law j (by simp only [List.mem_cons]; exact Or.inr hj)) next
      (completed+1) nextRoom (callback i w).state
    refine ⟨result,?_,?_,?_⟩
    · simpa only [loop,PV_V263_World.bind,ha,resourceWorld,PV_V263_World.lift,hpush] using hr
    · simp only [List.length_cons]
      rw [nextLength] at hlen
      omega
    · simp only [List.length_cons]
      omega

theorem granting_run {S A : Type} (osCodec : {B : Type} → Request B → Bytes)
    (vecCodec : PV_V263_MapSpine.VecCall → Bytes) (layouts : PV_V263_MapSpine.Layouts)
    (n : Usize) (k : Nat) (hk : k < 16) (callback : Nat → Q S A)
    (law : ∀ i, i < n.val → Total (callback i)) (w : State S) :
    ∃ result, (run (resourceWorld osCodec vecCodec) layouts n k callback w).outcome =
      .returned (.ok result) ∧ result.1.length = PV_RunJoin_WorkRange35.width n.val k ∧
      result.2 = result.1.length := by
  have widthBound := PV_RunJoin_WorkRange35.bounded n.val k hk
  have maxBound : n.val ≤ Usize.max := by
    have hn := n.hmax
    simp only [Usize.max,UScalarTy.numBits,Usize.numBits] at *
    omega
  have emptyLength : (alloc.vec.Vec.new A).length = 0 := rfl
  have room : (alloc.vec.Vec.new A).length + (PV_V263_Family.indices n.val k).length ≤ Usize.max := by
    simp only [emptyLength,Nat.zero_add,PV_V263_Family.indices,List.length_range']
    omega
  obtain ⟨result,hr,hlen,hcompleted⟩ := granting_loop osCodec vecCodec layouts k callback
    (PV_V263_Family.indices n.val k)
    (fun i hi => law i (PV_V263_Family.in_range n.val k i hk hi))
    (alloc.vec.Vec.new A) 0 room w
  refine ⟨result,?_,?_,?_⟩
  · simpa only [run,PV_V263_World.bind,resourceWorld] using hr
  · simpa only [emptyLength,Nat.zero_add,PV_V263_Family.indices,List.length_range'] using hlen
  · rw [emptyLength,Nat.zero_add] at hlen
    omega

#print axioms loop
#print axioms run
#print axioms granting_loop
#print axioms granting_run
end R1Z.PV_V263_VectorLoop
