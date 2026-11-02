import R1Z.PV_V263_GrantItems
/-! Full team resource success, without a supplied vector of worker answers.
Every deferred task executes its stored callback computation at its post-world. -/
set_option autoImplicit false
namespace R1Z.PV_V263_GrantTeam
open Aeneas Aeneas.Std PV_V263_World PV_V263_WorkerRequests PV_V263_WorkerControl
open PV_V263_GrantControl PV_V263_GrantItems
open PV_RJ4IDB (Bytes)
variable {S A : Type}
variable (osCodec : {B : Type} → Request B → Bytes)
variable (vecCodec : PV_V263_MapSpine.VecCall → Bytes)
variable (layouts : PV_V263_MapSpine.Layouts) (n : Nat) (callback : Nat → Q S A)

def IsOk {B : Type} (caught : Except Bytes B) : Prop := ∃ value, caught = .ok value

def GoodTask {B : Type} (task : PV_V263_DeferredJoin.Task S B) : Prop :=
  Returns IsOk task.action

theorem forks_good (law : CallbackLaw n callback) :
    Returns (fun tasks => ∀ task, task ∈ tasks → GoodTask task)
      (PV_V263_SourceSpine.forks (resourceWorld osCodec vecCodec) layouts n callback) := by
  apply traverse_returns
  intro k hk
  have bound : k < 16 := by simp only [List.mem_range'] at hk; omega
  have hf : Returns GoodTask (PV_V263_DeferredJoin.fork (grants osCodec) k
      (PV_V263_SourceSpine.caughtFamily (resourceWorld osCodec vecCodec) layouts n k callback)) := by
    intro w
    exact ⟨⟨k,w.nextHandle,_⟩,rfl,
      caught_family osCodec vecCodec layouts n callback k bound law⟩
  apply bind_returns GoodTask _ _ _ hf
  intro task ht
  apply bind_returns (fun _ => True) _ _ _ (vector_total osCodec vecCodec _)
  intro unit hunit
  exact pure_returns GoodTask task ht

theorem join_good {B : Type} (task : PV_V263_DeferredJoin.Task S B) (ht : GoodTask task) :
    Returns IsOk (PV_V263_DeferredJoin.join (grants osCodec) task) := by
  intro w
  obtain ⟨caught,hc,hp⟩ := ht w
  exact ⟨caught,by simp only [PV_V263_DeferredJoin.join,PV_V263_World.bind,hc,
    grants,PV_V263_World.lift],hp⟩

theorem join_chunks_good (length : Nat)
    (tasks : List (PV_V263_DeferredJoin.Task S (List (List A × Nat))))
    (law : ∀ task, task ∈ tasks → GoodTask task) :
    Returns (fun chunks => ∀ chunk, chunk ∈ chunks → IsOk chunk)
      (PV_V263_SourceSpine.joinChunks (resourceWorld osCodec vecCodec) layouts length tasks) := by
  induction tasks generalizing length with
  | nil => exact pure_returns _ [] (by intro a h; cases h)
  | cons task tasks ih =>
    apply bind_returns IsOk _ _ _ (join_good osCodec task (law task (by simp)))
    intro caught hc
    apply bind_returns (fun _ => True) _ _ _ (vector_total osCodec vecCodec _)
    intro unit hunit
    apply bind_returns _ _ _ _
      (ih (length+1) (fun t ht => law t (by simp only [List.mem_cons]; exact Or.inr ht)))
    intro rest hr
    apply pure_returns
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with hx | hx
    · subst x; exact hc
    · exact hr x hx

theorem merge_total (length : Nat) (chunks : List (Except Bytes (List (List A × Nat))))
    (law : ∀ chunk, chunk ∈ chunks → IsOk chunk) :
    Total (PV_V263_SourceSpine.mergePool (resourceWorld osCodec vecCodec) layouts length chunks) := by
  induction chunks generalizing length with
  | nil => exact pure_returns _ [] trivial
  | cons chunk chunks ih =>
    obtain ⟨value,hvalue⟩ := law chunk (by simp)
    subst chunk
    apply bind_total _ _ (vector_total osCodec vecCodec _)
    intro unit
    apply bind_total _ _ (vector_total osCodec vecCodec _)
    intro unit
    apply bind_total _ _ (ih (length+value.length)
      (fun c hc => law c (by simp only [List.mem_cons]; exact Or.inr hc)))
    intro rest
    exact pure_returns _ (value++rest) trivial

theorem append_total (length k : Nat) (chunks : List (List A × Nat)) :
    Total (PV_V263_SourceSpine.appendItems (resourceWorld osCodec vecCodec) layouts length k chunks) := by
  induction chunks generalizing length k with
  | nil => exact pure_returns _ [] trivial
  | cons chunk chunks ih =>
    rcases chunk with ⟨value,completed⟩
    apply bind_total _ _ (vector_total osCodec vecCodec _)
    intro unit
    apply bind_total _ _ (vector_total osCodec vecCodec _)
    intro unit
    apply bind_total _ _ (ih (length+value.length) (k+1))
    intro rest
    exact pure_returns _ (value++rest) trivial

#print axioms IsOk
#print axioms GoodTask
#print axioms forks_good
#print axioms join_good
#print axioms join_chunks_good
#print axioms merge_total
#print axioms append_total
end R1Z.PV_V263_GrantTeam
