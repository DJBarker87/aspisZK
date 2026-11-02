import R1Z.PV_V263_MapSpine
/-! Successful-output invariants, NOT termination or existence hypotheses.
These hold for arbitrary stateful callbacks/OS answers. A failed/divergent/
faulted/exhausted computation does not manufacture a successful vector. -/
set_option autoImplicit false
namespace R1Z.PV_V263_OutputShape
open Aeneas Aeneas.Std PV_V263_World PV_V263_WorkerControl

def Post {S A : Type} (p : A → Prop) (action : Q S A) : Prop :=
  ∀ w a, (action w).outcome = .returned (.ok a) → p a

theorem bind_success {S A B : Type} (action : Q S A) (next : A → Q S B)
    (w : State S) (b : B)
    (h : (PV_V263_World.bind action next w).outcome = .returned (.ok b)) :
    ∃ a, (action w).outcome = .returned (.ok a) ∧
      (next a (action w).state).outcome = .returned (.ok b) := by
  cases ha : (action w).outcome with
  | fault e => simp only [PV_V263_World.bind,ha] at h; cases h
  | exhausted => simp only [PV_V263_World.bind,ha] at h; cases h
  | returned r =>
    cases r with
    | fail e => simp only [PV_V263_World.bind,ha] at h; cases h
    | div => simp only [PV_V263_World.bind,ha] at h; cases h
    | ok a => exact ⟨a,rfl,by simpa only [PV_V263_World.bind,ha] using h⟩

theorem pure_post {S A : Type} (p : A → Prop) (a : A) (h : p a) :
    Post (S := S) p (PV_V263_World.lift (.ok a)) := by
  intro w b hb
  cases hb
  exact h

theorem bind_post {S A B : Type} (p : A → Prop) (q : B → Prop)
    (action : Q S A) (next : A → Q S B) (ha : Post p action)
    (hn : ∀ a, p a → Post q (next a)) :
    Post q (PV_V263_World.bind action next) := by
  intro w b h
  obtain ⟨a,one,two⟩ := bind_success action next w b h
  exact hn a (ha w a one) (action w).state b two

theorem bind_any {S A B : Type} (q : B → Prop) (action : Q S A) (next : A → Q S B)
    (hn : ∀ a, Post q (next a)) : Post q (PV_V263_World.bind action next) :=
  bind_post (fun _ => True) q action next (fun _ _ _ => trivial) (fun a _ => hn a)

theorem traversal_length {S A : Type} (callback : Nat → Q S A) (ids : List Nat) :
    Post (fun (values : List A) => values.length = ids.length) (PV_V263_WorkerControl.traverse callback ids) := by
  induction ids with
  | nil => exact pure_post _ [] rfl
  | cons i ids ih =>
    exact bind_any (fun (values : List A) => values.length = (i::ids).length)
      (callback i) _ (fun a =>
        bind_post (fun (values : List A) => values.length = ids.length)
          (fun (values : List A) => values.length = (i::ids).length)
          (PV_V263_WorkerControl.traverse callback ids)
          (fun rest => PV_V263_World.lift (.ok (a::rest))) ih
          (fun rest hr => pure_post _ (a::rest)
            (by simpa only [List.length_cons] using congrArg Nat.succ hr)))

/-- The source item vector has exactly the requested width whenever it returns;
no callback result, vector value or successful run is assumed. -/
theorem items_length {S A : Type} (runtime : PV_V263_MapSpine.Runtime S)
    (layouts : PV_V263_MapSpine.Layouts) (n k : Nat) (callback : Nat → Q S A) :
    Post (fun (values : List A) => values.length = PV_RunJoin_WorkRange35.width n k)
      (PV_V263_MapSpine.items runtime layouts n k callback) := by
  change Post _ (PV_V263_World.bind _ _)
  apply bind_any
  intro unit
  simpa only [PV_V263_Family.indices,List.length_range'] using
    traversal_length callback (PV_V263_Family.indices n k)

/-- One outer family contains one pair, with completed equal to item length.
This is the second range layer, distinct from the original item count. -/
theorem family_shape {S A : Type} (runtime : PV_V263_MapSpine.Runtime S)
    (layouts : PV_V263_MapSpine.Layouts) (n k : Nat) (callback : Nat → Q S A) :
    Post (fun (chunks : List (List A × Nat)) => ∃ values, chunks = [(values,values.length)] ∧
      values.length = PV_RunJoin_WorkRange35.width n k)
      (PV_V263_MapSpine.family runtime layouts n k callback) := by
  let predicate := fun (chunks : List (List A × Nat)) => ∃ values,
    chunks = [(values,values.length)] ∧ values.length = PV_RunJoin_WorkRange35.width n k
  exact bind_any predicate (runtime.vector (.collect 1 k 1 layouts.family)) _
    (fun _ => bind_post
      (fun (values : List A) => values.length = PV_RunJoin_WorkRange35.width n k)
      predicate (PV_V263_MapSpine.items runtime layouts n k callback)
      (fun values => PV_V263_World.lift (.ok [(values,values.length)]))
      (items_length runtime layouts n k callback)
      (fun values hv => pure_post predicate [(values,values.length)] ⟨values,rfl,hv⟩))

#print axioms Post
#print axioms bind_success
#print axioms pure_post
#print axioms bind_post
#print axioms bind_any
#print axioms traversal_length
#print axioms items_length
#print axioms family_shape
end R1Z.PV_V263_OutputShape
