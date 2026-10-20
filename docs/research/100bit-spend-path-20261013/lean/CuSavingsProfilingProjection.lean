import CuSavingsProfilingMarker
/-! Fixed program callback projection. SDK diagnostic logs and compute-unit
reports are the erased effect channel. Application events remain observable.
This is a callback contract under the existing sufficient-reference-resource
runtime boundary; it does not identify resource exhaustion with success. -/
set_option autoImplicit false
namespace AspisR1.CuSavingsProfilingProjection
open Aeneas Aeneas.Std Result AspisR1Profiling

inductive Diagnostic where
  | message : String → Diagnostic
  | computeUnits : Diagnostic

def message (phase : Phase) : String := match phase with
  | .QueryPart i j => "r1:query-part:" ++ toString i.val ++ ":" ++ toString j.val
  | .SemanticPart i => "r1:semantic-part:" ++ toString i.val
  | .Parsed => "r1:parsed"
  | .Semantic => "r1:semantic"
  | .Prepare => "r1:prepare"
  | .CheckpointRead => "r1:checkpoint-read"
  | .CheckpointWrite => "r1:checkpoint-write"
  | .Merkle i => "r1:merkle:" ++ toString i.val
  | .Query i => "r1:query:" ++ toString i.val
  | .Relation => "r1:relation"
  | .Final => "r1:final"

/-- Exact two SDK effects in the fixed program mark callback. -/
def fixedEvents (phase : Phase) : List Diagnostic := [.message (message phase),.computeUnits]

inductive Event (App : Type) where
  | diagnostic : Diagnostic → Event App
  | application : App → Event App

def project {App : Type} (events : List (Event App)) : List App :=
  events.filterMap (fun event => match event with
    | .diagnostic _ => none
    | .application value => some value)

def callbackEvents {App : Type} (phase : Phase) : List (Event App) :=
  (fixedEvents phase).map Event.diagnostic

theorem callback_trace_erased {App : Type} (phase : Phase) :
    project (callbackEvents (App:=App) phase) = [] := rfl

theorem application_trace_preserved {App : Type} (phase : Phase)
    (before after : List (Event App)) :
    project (before ++ callbackEvents phase ++ after) = project (before ++ after) := by
  simp only [project,List.filterMap_append]
  have h := callback_trace_erased (App:=App) phase
  change (callbackEvents (App:=App) phase).filterMap _ = [] at h
  rw [h]
  simp only [List.append_nil,List.nil_append]

/-- The resource-qualified standard SDK contract returns Unit after private
formatting/logging effects. After projection its exact observable return is
Unit. This definition is not a model of failing diagnostic execution. -/
def projectedCallback (_phase : Phase) : Result Unit := .ok ()

def dispatcher (observer : Option (Phase → Result Unit)) : Phase → Result Unit :=
  fun phase => mark observer phase

theorem actual_dispatcher_eq :
    dispatcher (some projectedCallback) = dispatcher none := rfl

/-- Source-factorized closure over the sole observer dispatcher. The context
may return application state, ordered cryptographic calls, checkpoint bytes,
source errors or divergence, without any totality premise on the context. -/
theorem source_context_eq {A : Type} (context : (Phase → Result Unit) → A) :
    context (dispatcher (some projectedCallback)) = context (dispatcher none) := rfl

/-- Transfer a reference contract through exact dispatcher substitution. -/
theorem transfer {A : Type} (context : (Phase → Result Unit) → A)
    (contract : A → Prop) (reference : contract (context (dispatcher (some projectedCallback)))) :
    contract (context (dispatcher none)) := reference

#print axioms callback_trace_erased
#print axioms application_trace_preserved
#print axioms actual_dispatcher_eq
#print axioms source_context_eq
#print axioms transfer
end AspisR1.CuSavingsProfilingProjection
