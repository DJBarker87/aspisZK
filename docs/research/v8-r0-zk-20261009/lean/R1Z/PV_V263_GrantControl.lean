import R1Z.PV_V263_SourceSpine
import R1Z.PV_V263_FamilyWorld
/-! Compositional success in a constructed primitive-resource world.
These are interpreter laws, not source/native adequacy or callback laws. -/
set_option autoImplicit false
namespace R1Z.PV_V263_GrantControl
open Aeneas Aeneas.Std PV_V263_World PV_V263_WorkerRequests PV_V263_WorkerControl
open PV_RJ4IDB (Bytes NativeEvent)

def Returns {S A : Type} (p : A → Prop) (action : Q S A) : Prop :=
  ∀ w, ∃ a, (action w).outcome = .returned (.ok a) ∧ p a

def Total {S A : Type} (action : Q S A) : Prop := Returns (fun _ => True) action

def resourceWorld {S : Type} (osCodec : {A : Type} → Request A → Bytes)
    (vecCodec : PV_V263_MapSpine.VecCall → Bytes) : PV_V263_MapSpine.Runtime S where
  os := grants osCodec
  vector := fun call w => ⟨.returned (.ok ()),w,
    [NativeEvent.side [118,50,54,51,118] (vecCodec call)]⟩

theorem pure_returns {S A : Type} (p : A → Prop) (a : A) (ha : p a) :
    Returns (S := S) p (lift (.ok a)) := fun _ => ⟨a,rfl,ha⟩

theorem weaken {S A : Type} (p q : A → Prop) (action : Q S A)
    (h : Returns p action) (imp : ∀ a, p a → q a) : Returns q action := by
  intro w
  obtain ⟨a,ha,hp⟩ := h w
  exact ⟨a,ha,imp a hp⟩

theorem bind_returns {S A B : Type} (p : A → Prop) (q : B → Prop)
    (action : Q S A) (next : A → Q S B) (ha : Returns p action)
    (hn : ∀ a, p a → Returns q (next a)) : Returns q (PV_V263_World.bind action next) := by
  intro w
  obtain ⟨a,one,hp⟩ := ha w
  obtain ⟨b,two,hq⟩ := hn a hp (action w).state
  exact ⟨b,by simp only [PV_V263_World.bind,one,two],hq⟩

theorem bind_total {S A B : Type} (action : Q S A) (next : A → Q S B)
    (ha : Total action) (hn : ∀ a, Total (next a)) :
    Total (PV_V263_World.bind action next) :=
  bind_returns _ _ action next ha (fun a _ => hn a)

theorem vector_total {S : Type} (osCodec : {A : Type} → Request A → Bytes)
    (vecCodec : PV_V263_MapSpine.VecCall → Bytes) (call : PV_V263_MapSpine.VecCall) :
    Total ((resourceWorld (S := S) osCodec vecCodec).vector call) :=
  fun _ => ⟨(),rfl,trivial⟩

theorem os_total {S A : Type} (osCodec : {B : Type} → Request B → Bytes)
    (request : Request A) : Total ((grants (S := S) osCodec).answer request) := by
  intro w
  cases request <;> exact ⟨_,rfl,trivial⟩

theorem traverse_returns {S A : Type} (p : A → Prop) (callback : Nat → Q S A)
    (ids : List Nat) (law : ∀ i, i ∈ ids → Returns p (callback i)) :
    Returns (fun values => ∀ a, a ∈ values → p a)
      (PV_V263_WorkerControl.traverse callback ids) := by
  induction ids with
  | nil => exact pure_returns _ [] (by intro a h; cases h)
  | cons i ids ih =>
    apply bind_returns p _ (callback i) _ (law i (by simp))
    intro a ha
    apply bind_returns _ _ (PV_V263_WorkerControl.traverse callback ids) _
      (ih (fun j hj => law j (by simp only [List.mem_cons]; exact Or.inr hj)))
    intro rest hr
    apply pure_returns
    intro b hb
    simp only [List.mem_cons] at hb
    rcases hb with hb | hb
    · subst b; exact ha
    · exact hr b hb

theorem active_returns {S A : Type} (osCodec : {B : Type} → Request B → Bytes)
    (profile : Profile) (thread : Nat) (p : A → Prop) (action : Q S A)
    (law : Returns p action) : Returns p (withActive (grants osCodec) profile thread action) := by
  intro w
  let w' : State S := {w with activeTLS := (thread,true)::w.activeTLS.filter (fun p => p.1 != thread)}
  obtain ⟨a,ha,hp⟩ := law w'
  refine ⟨a,?_,hp⟩
  simp only [withActive,PV_V263_World.bind,grants]
  change (finalize profile action
    ((grants osCodec).answer (.tlsRestore thread ((w.activeTLS.lookup thread).getD false))) w').outcome = _
  simp only [finalize,ha,grants]

theorem caught_returns {S A : Type} (profile : Profile) (action : Q S A)
    (law : Total action) :
    Returns (fun caught => ∃ a, caught = Except.ok a) (catchPanic profile action) := by
  intro w
  obtain ⟨a,ha,_⟩ := law w
  exact ⟨.ok a,by simp only [catchPanic,ha],⟨a,rfl⟩⟩

#print axioms Returns
#print axioms Total
#print axioms resourceWorld
#print axioms pure_returns
#print axioms weaken
#print axioms bind_returns
#print axioms bind_total
#print axioms vector_total
#print axioms os_total
#print axioms traverse_returns
#print axioms active_returns
#print axioms caught_returns
end R1Z.PV_V263_GrantControl
