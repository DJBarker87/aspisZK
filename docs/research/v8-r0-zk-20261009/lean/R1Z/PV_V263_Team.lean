import R1Z.PV_V263_WorkerControl
/-! Thread-request projection of the exact source loop 1..THREADS. Allocation
of the handles Vec and scope cleanup are NOT erased from a credited source
model: this file proves the projection only, not V263's complete association.
The granting world is stateful; denied requests retain the fault prefix. -/
set_option autoImplicit false
namespace R1Z.PV_V263_Team
open Aeneas Aeneas.Std PV_V263_World PV_V263_WorkerRequests PV_V263_WorkerControl
open PV_RJ4IDB (Bytes)

def launch {S : Type} (runtime : Runtime S) : List Nat → Q S (List Nat) :=
  PV_V263_WorkerControl.traverse (spawn runtime)

def team {S : Type} (runtime : Runtime S) : Q S (List Nat) :=
  launch runtime (List.range' 1 15)

theorem grant_launch {S : Type} (encode : {A : Type} → Request A → Bytes)
    (ids : List Nat) (w : State S) :
    ∃ handles, (launch (grants encode) ids w).outcome = .returned (.ok handles) :=
  traverse_total (spawn (grants encode)) (fun i v => ⟨v.nextHandle,grant_spawn encode i v⟩) ids w

/-- Stronger than bare existence: handle values and counter advance are derived
from the granting world, never supplied as a successful vector hypothesis. -/
theorem grant_exact {S : Type} (encode : {A : Type} → Request A → Bytes)
    (ids : List Nat) (w : State S) :
    (launch (grants encode) ids w).outcome = .returned (.ok (List.range' w.nextHandle ids.length)) ∧
    (launch (grants encode) ids w).state.nextHandle = w.nextHandle + ids.length := by
  induction ids generalizing w with
  | nil => exact ⟨rfl,by simp only [launch,PV_V263_WorkerControl.traverse,PV_V263_World.lift,List.length_nil,Nat.add_zero]⟩
  | cons i is ih =>
    let w' : State S := {w with liveHandles := w.nextHandle::w.liveHandles,nextHandle := w.nextHandle+1}
    obtain ⟨ho,hs⟩ := ih w'
    change (launch (grants encode) is w').outcome = _ at ho
    constructor
    · simp only [launch,PV_V263_WorkerControl.traverse,PV_V263_World.bind,spawn,grants,PV_V263_World.lift] at ho ⊢
      rw [ho]
      rfl
    · simp only [launch,PV_V263_WorkerControl.traverse,PV_V263_World.bind,spawn,grants,PV_V263_World.lift] at ho ⊢
      rw [ho]
      change (launch (grants encode) is w').state.nextHandle = _
      rw [hs]
      simp only [w',List.length_cons]
      omega

theorem fifteen {S : Type} (encode : {A : Type} → Request A → Bytes) (w : State S) :
    (team (grants encode) w).outcome = .returned (.ok (List.range' w.nextHandle 15)) ∧
    (team (grants encode) w).state.nextHandle = w.nextHandle+15 := by
  simpa only [team,List.length_range'] using grant_exact encode (List.range' 1 15) w

theorem deny_first {S : Type} (encode : {A : Type} → Request A → Bytes)
    (code : Int) (i : Nat) (is : List Nat) (w : State S) :
    launch (denies encode code) (i::is) w =
      ⟨.fault (.spawnDenied code),w,[.side [118,50,54,51] (encode (.spawn i))]⟩ := rfl

/-- Successful resource witnesses coexist with a faulting world. This is NOT
Nonempty P: there are no callback or captured-run success premises here. -/
theorem worlds {S : Type} (encode : {A : Type} → Request A → Bytes) (w : State S) (code : Int) :
    (∃ handles, (team (grants encode) w).outcome = .returned (.ok handles)) ∧
    sourceProjection (launch (denies encode code) [1] w).outcome = none := by
  exact ⟨grant_launch encode _ w,rfl⟩

#print axioms launch
#print axioms team
#print axioms grant_launch
#print axioms grant_exact
#print axioms fifteen
#print axioms deny_first
#print axioms worlds
end R1Z.PV_V263_Team
