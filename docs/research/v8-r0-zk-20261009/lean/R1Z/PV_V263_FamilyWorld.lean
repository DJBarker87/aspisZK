import R1Z.PV_V263_Family
/-! A real resource-success component, with STATEFUL callbacks and post-world
TLS restoration. The actual callback law is deliberately not asserted here.
No Nonempty P claim or new endpoint premise follows from this module. -/
set_option autoImplicit false
namespace R1Z.PV_V263_FamilyWorld
open Aeneas Aeneas.Std PV_V263_World PV_V263_WorkerRequests PV_V263_WorkerControl
open PV_V263_PublicRequests (Layout)
open PV_RJ4IDB (Bytes)

theorem finalize_return {S A : Type} (profile : Profile) (action : Q S A)
    (drop : Q S Unit) (w : State S) (a : A)
    (ha : (action w).outcome = .returned (.ok a))
    (hd : (drop (action w).state).outcome = .returned (.ok ())) :
    finalize profile action drop w =
      ⟨.returned (.ok a),(drop (action w).state).state,
        (action w).events ++ (drop (action w).state).events⟩ := by
  simp only [finalize,ha,hd]

theorem granting_active {S A : Type} (encode : {B : Type} → Request B → Bytes)
    (profile : Profile) (thread : Nat) (action : Q S A)
    (law : ∀ w, ∃ a, (action w).outcome = .returned (.ok a)) (w : State S) :
    ∃ a, (withActive (grants encode) profile thread action w).outcome = .returned (.ok a) := by
  let w' : State S := {w with activeTLS := (thread,true)::w.activeTLS.filter (fun p => p.1 != thread)}
  obtain ⟨a,ha⟩ := law w'
  refine ⟨a,?_⟩
  simp only [withActive,PV_V263_World.bind,grants]
  change (finalize profile action
    ((grants encode).answer (.tlsRestore thread ((w.activeTLS.lookup thread).getD false))) w').outcome = _
  simp only [finalize,ha,grants]

/-- Counts can be any natural n, including each reached public count. Resource
success here is constructed by grants; callback success still requires the
actual encoder/semantic proof and cannot be supplied as an endpoint premise. -/
theorem granting_family {S A : Type} (encode : {B : Type} → Request B → Bytes)
    (profile : Profile) (layout : Layout) (n k : Nat) (hk : k < 16)
    (callback : Nat → Q S A)
    (law : ∀ i, i < n → ∀ w, ∃ a, (callback i w).outcome = .returned (.ok a))
    (w : State S) :
    ∃ values, (PV_V263_Family.run (grants encode) profile layout n k callback w).outcome =
      .returned (.ok (.ok values)) := by
  let action := PV_V263_Family.body (grants encode) layout n k callback
  have total : ∀ v, ∃ values, (action v).outcome = .returned (.ok values) :=
    PV_V263_Family.granting_body encode layout n k hk callback law
  have caught : ∀ v, ∃ result, (catchPanic profile action v).outcome = .returned (.ok result) := by
    intro v
    obtain ⟨values,h⟩ := total v
    exact ⟨.ok values,by simp only [catchPanic,h]⟩
  let w' : State S := {w with activeTLS := (k,true)::w.activeTLS.filter (fun p => p.1 != k)}
  obtain ⟨values,h⟩ := total w'
  refine ⟨values,?_⟩
  simp only [PV_V263_Family.run,withActive,PV_V263_World.bind,grants]
  change (finalize profile (catchPanic profile action)
    ((grants encode).answer (.tlsRestore k ((w.activeTLS.lookup k).getD false))) w').outcome = _
  have hc : (catchPanic profile action w').outcome = .returned (.ok (.ok values)) := by
    simp only [catchPanic,h]
  simp only [finalize,hc,grants]

#print axioms finalize_return
#print axioms granting_active
#print axioms granting_family
end R1Z.PV_V263_FamilyWorld
