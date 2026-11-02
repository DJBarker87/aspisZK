import R1Z.PV_V263_VecSpine
/-! Full-outcome initialized-store refinement for the TrustedLen range-map
collector. Faults, finite exhaustion, source failure/divergence, post-world and
all events survive. No callback-success or successful-vector premise. -/
set_option autoImplicit false
namespace R1Z.PV_V263_CollectBinding
open Aeneas Aeneas.Std PV_V263_World

def mapResult {A B : Type} (f : A → B) : Result A → Result B
  | .ok a => .ok (f a)
  | .fail e => .fail e
  | .div => .div

def mapOutcome {A B : Type} (f : A → B) : Outcome A → Outcome B
  | .returned r => .returned (mapResult f r)
  | .fault e => .fault e
  | .exhausted => .exhausted

def mapRun {S A B : Type} (f : A → B) (r : Run S A) : Run S B :=
  ⟨mapOutcome f r.outcome,r.state,r.events⟩

theorem compose {S A B C : Type} (f : A → B) (g : B → C) (r : Run S A) :
    mapRun g (mapRun f r) = mapRun (fun a => g (f a)) r := by
  cases r with | mk outcome state events =>
    cases outcome with
    | fault e => rfl
    | exhausted => rfl
    | returned result => cases result <;> rfl

def prefix {S A : Type} (events : List PV_RJ4IDB.NativeEvent) (r : Run S A) : Run S A :=
  ⟨r.outcome,r.state,events++r.events⟩

theorem map_prefix {S A B : Type} (f : A → B) (events : List PV_RJ4IDB.NativeEvent)
    (r : Run S A) : mapRun f (prefix events r) = prefix events (mapRun f r) := rfl

theorem pure_bind {S A B : Type} (f : A → B) (m : Q S A) (w : State S) :
    PV_V263_World.bind m (fun a => lift (.ok (f a))) w = mapRun f (m w) := by
  cases h : (m w).outcome with
  | fault e => simp only [PV_V263_World.bind,h,mapRun,mapOutcome]
  | exhausted => simp only [PV_V263_World.bind,h,mapRun,mapOutcome]
  | returned result => cases result <;>
      simp only [PV_V263_World.bind,h,mapRun,mapOutcome,mapResult,lift,List.append_nil]

theorem bind_ok {S A B : Type} (m : Q S A) (k : A → Q S B) (w : State S) (a : A)
    (h : (m w).outcome = .returned (.ok a)) :
    PV_V263_World.bind m k w = prefix (m w).events (k a (m w).state) := by
  simp only [PV_V263_World.bind,h,prefix]

/-- Equality of complete runs. Room is an initial-capacity bound and has no
callback-answer or successful-vector dependency. -/
theorem stores {S A : Type} (runtime : PV_V263_VecSpine.Runtime S)
    (f : Nat → Q S A) (ids : List Nat) (out : alloc.vec.Vec A)
    (room : out.length+ids.length ≤ Usize.max) (w : State S) :
    mapRun (fun v : alloc.vec.Vec A => v.val)
      (PV_V263_VecSpine.collectLoop runtime f ids out w) =
    mapRun (fun values => out.val++values)
      (PV_V263_WorkerControl.traverse f ids w) := by
  induction ids generalizing out w with
  | nil =>
    change mapRun (fun v : alloc.vec.Vec A => v.val) (lift (.ok out) w) =
      mapRun (fun values => out.val++values) (lift (.ok []) w)
    simp only [mapRun,mapOutcome,mapResult,lift,List.append_nil]
  | cons i ids ih =>
    change mapRun (fun v : alloc.vec.Vec A => v.val)
      (PV_V263_World.bind (f i) (fun a =>
        PV_V263_World.bind (PV_V263_VecSpine.value runtime (alloc.vec.Vec.push out a))
          (fun next => PV_V263_VecSpine.collectLoop runtime f ids next)) w) = _
    cases hf : (f i w).outcome with
    | fault e => simp only [PV_V263_World.bind,hf,PV_V263_WorkerControl.traverse,
        mapRun,mapOutcome]
    | exhausted => simp only [PV_V263_World.bind,hf,PV_V263_WorkerControl.traverse,
        mapRun,mapOutcome]
    | returned result =>
      cases result with
      | fail e => simp only [PV_V263_World.bind,hf,PV_V263_WorkerControl.traverse,
          mapRun,mapOutcome,mapResult]
      | div => simp only [PV_V263_World.bind,hf,PV_V263_WorkerControl.traverse,
          mapRun,mapOutcome,mapResult]
      | ok a =>
        have bound : out.length+1 ≤ Usize.max := by
          simp only [List.length_cons] at room
          omega
        obtain ⟨next,hpush,hvalues⟩ := PV_RunJoin_Vector44.push out a bound
        have hlength : next.length=out.length+1 := by
          change next.val.length=out.val.length+1
          rw [hvalues,List.length_append,List.length_singleton]
        have remaining : next.length+ids.length ≤ Usize.max := by
          rw [hlength]
          simp only [List.length_cons] at room
          omega
        have recursion := ih next remaining (f i w).state
        have functions : (fun values : List A => next.val++values) =
            (fun values => out.val++(a::values)) := by
          funext values
          rw [hvalues,List.append_assoc]
          rfl
        rw [functions] at recursion
        have leftStep : PV_V263_World.bind (f i) (fun a =>
            PV_V263_World.bind (PV_V263_VecSpine.value runtime (alloc.vec.Vec.push out a))
              (fun next => PV_V263_VecSpine.collectLoop runtime f ids next)) w =
            prefix (f i w).events (PV_V263_VecSpine.collectLoop runtime f ids next (f i w).state) := by
          rw [bind_ok _ _ _ _ hf]
          simp only [PV_V263_VecSpine.value,hpush,PV_V263_World.bind,lift,List.nil_append]
        rw [leftStep,map_prefix,recursion]
        change _ = mapRun (fun values => out.val++values)
          (PV_V263_World.bind (f i) (fun a => PV_V263_World.bind
            (PV_V263_WorkerControl.traverse f ids) (fun values => lift (.ok (a::values)))) w)
        rw [bind_ok _ _ _ _ hf,pure_bind,map_prefix,compose]

#print axioms mapResult
#print axioms mapOutcome
#print axioms mapRun
#print axioms compose
#print axioms prefix
#print axioms map_prefix
#print axioms pure_bind
#print axioms bind_ok
#print axioms stores
end R1Z.PV_V263_CollectBinding
