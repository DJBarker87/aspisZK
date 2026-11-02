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

/-- This is equality of complete runs, not just successful lengths. The room
condition is an initial-capacity bound, independent of callback answers. -/
theorem stores {S A : Type} (runtime : PV_V263_VecSpine.Runtime S)
    (f : Nat → Q S A) (ids : List Nat) (out : alloc.vec.Vec A)
    (room : out.length+ids.length ≤ Usize.max) (w : State S) :
    mapRun (fun v : alloc.vec.Vec A => v.val)
      (PV_V263_VecSpine.collectLoop runtime f ids out w) =
    mapRun (fun values => out.val++values)
      (PV_V263_WorkerControl.traverse f ids w) := by
  induction ids generalizing out w with
  | nil => simp only [PV_V263_VecSpine.collectLoop,PV_V263_WorkerControl.traverse,
      mapRun,mapOutcome,mapResult,PV_V263_World.lift,List.append_nil]
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
        have rec := ih next remaining (f i w).state
        have functions : (fun values : List A => next.val++values) =
            (fun values => out.val++(a::values)) := by
          funext values
          rw [hvalues,List.append_assoc]
          rfl
        rw [functions] at rec
        simp only [PV_V263_World.bind,hf,PV_V263_VecSpine.value,hpush,
          PV_V263_World.lift,PV_V263_WorkerControl.traverse] 
        have ho := congrArg Run.outcome rec
        have hs := congrArg Run.state rec
        have he := congrArg Run.events rec
        simp only [mapRun] at ho hs he
        simp only [mapRun,mapOutcome,mapResult]
        rw [hs,he]
        cases hr : (PV_V263_WorkerControl.traverse f ids (f i w).state).outcome with
        | fault e => simpa only [mapOutcome,hr] using congrArg
            (fun outcome => Run.mk outcome
              (PV_V263_WorkerControl.traverse f ids (f i w).state).state
              ((f i w).events++(PV_V263_WorkerControl.traverse f ids (f i w).state).events)) ho
        | exhausted => simpa only [mapOutcome,hr] using congrArg
            (fun outcome => Run.mk outcome
              (PV_V263_WorkerControl.traverse f ids (f i w).state).state
              ((f i w).events++(PV_V263_WorkerControl.traverse f ids (f i w).state).events)) ho
        | returned r => cases r <;> simpa only [mapOutcome,mapResult,hr,
            PV_V263_World.lift,List.append_nil,List.append_assoc] using congrArg
            (fun outcome => Run.mk outcome
              (PV_V263_WorkerControl.traverse f ids (f i w).state).state
              ((f i w).events++(PV_V263_WorkerControl.traverse f ids (f i w).state).events)) ho

#print axioms mapResult
#print axioms mapOutcome
#print axioms mapRun
#print axioms compose
#print axioms stores
end R1Z.PV_V263_CollectBinding
