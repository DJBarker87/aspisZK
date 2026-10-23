import Std

/-! Local effect algebra, indexed by one execution identifier E and fixed
original inputs. NO native adapter instance or source refinement is provided.
The caller must interpret cuts of E into these observations. Effects include
queries, syscalls, logs, allocations and actual destructor calls in order. -/
set_option autoImplicit false
namespace AspisR1.S2D

inductive Exit (Error Value : Type) where
  | returned (value : Value)
  | rejected (error : Error)
  | aborted
  deriving DecidableEq

/-- E/original are indices, never existentially selected child executions. -/
structure Cut {Native Input : Type} (E : Native) (original : Input)
    (State Event Error Value : Type) where
  state : State
  effects : List Event
  exit : Exit Error Value

variable {Native Input State Event Error A B C : Type}
variable {E : Native} {original : Input}

/-- Result `?`: the suffix receives exactly the preceding state and value.
Rejected and aborted observations never evaluate the suffix. -/
def thenDo (p : Cut E original State Event Error A)
    (next : State → A → Cut E original State Event Error B) :
    Cut E original State Event Error B :=
  match p.exit with
  | .returned a =>
      let q := next p.state a
      ⟨q.state, p.effects ++ q.effects, q.exit⟩
  | .rejected e => ⟨p.state, p.effects, .rejected e⟩
  | .aborted => ⟨p.state, p.effects, .aborted⟩

/-- A mapped error may log or otherwise affect state. The mapper's own
ordered effects are retained rather than treating map_err as a pure rename. -/
def mapError (p : Cut E original State Event Error A)
    (mapper : State → Error → State × List Event × Error) :
    Cut E original State Event Error A :=
  match p.exit with
  | .rejected e =>
      let q := mapper p.state e
      ⟨q.1, p.effects ++ q.2.1, .rejected q.2.2⟩
  | .returned a => ⟨p.state, p.effects, .returned a⟩
  | .aborted => ⟨p.state, p.effects, .aborted⟩

/-- Only a normal return/rejection runs the supplied cleanup. Its state and
ordered effects must come from E's actual cleanup cut; this is not an assumed
universal account frame. An abort explicitly carries no invented Drop suffix. -/
def finish (p : Cut E original State Event Error A)
    (cleanup : State → State × List Event) : Cut E original State Event Error A :=
  match p.exit with
  | .aborted => p
  | _ => let q := cleanup p.state; ⟨q.1, p.effects ++ q.2, p.exit⟩

theorem rejected_short_circuit (s : State) (events : List Event) (e : Error)
    (next : State → A → Cut E original State Event Error B) :
    thenDo (⟨s, events, .rejected e⟩ : Cut E original State Event Error A) next =
      ⟨s, events, .rejected e⟩ := rfl

theorem aborted_short_circuit (s : State) (events : List Event)
    (next : State → A → Cut E original State Event Error B) :
    thenDo (⟨s, events, .aborted⟩ : Cut E original State Event Error A) next =
      ⟨s, events, .aborted⟩ := rfl

theorem rejected_cleanup (s : State) (events : List Event) (e : Error)
    (cleanup : State → State × List Event) :
    finish (⟨s, events, .rejected e⟩ : Cut E original State Event Error A) cleanup =
      ⟨(cleanup s).1, events ++ (cleanup s).2, .rejected e⟩ := rfl

theorem abort_has_no_normal_cleanup (s : State) (events : List Event)
    (cleanup : State → State × List Event) :
    finish (⟨s, events, .aborted⟩ : Cut E original State Event Error A) cleanup =
      ⟨s, events, .aborted⟩ := rfl

theorem mapped_rejection_retains_effects (s : State) (events : List Event) (e : Error)
    (mapper : State → Error → State × List Event × Error) :
    mapError (⟨s, events, .rejected e⟩ : Cut E original State Event Error A) mapper =
      ⟨(mapper s e).1, events ++ (mapper s e).2.1, .rejected (mapper s e).2.2⟩ := rfl

theorem thenDo_associative (p : Cut E original State Event Error A)
    (f : State → A → Cut E original State Event Error B)
    (g : State → B → Cut E original State Event Error C) :
    thenDo (thenDo p f) g = thenDo p (fun s a => thenDo (f s a) g) := by
  cases p with
  | mk s events result =>
    cases result with
    | rejected e => rfl
    | aborted => rfl
    | returned a =>
      simp only [thenDo]
      cases f s a with
      | mk s' events' result' =>
        cases result' <;> simp only [thenDo, List.append_assoc]

/-- Projection does not filter by acceptance. Rejected oracle histories are
included, and duplicates and order survive. -/
def queries {Query : Type} (select : Event → Option Query)
    (p : Cut E original State Event Error A) : List Query :=
  p.effects.filterMap select

theorem rejection_queries_retained {Query : Type} (select : Event → Option Query)
    (s : State) (events : List Event) (e : Error)
    (cleanup : State → State × List Event) :
    queries select (finish (⟨s, events, .rejected e⟩ : Cut E original State Event Error A) cleanup) =
      events.filterMap select ++ ((cleanup s).2).filterMap select := by
  exact List.filterMap_append

theorem successful_prefix_then_rejection (s : State) (before : List Event) (a : A)
    (s' : State) (childEvents : List Event) (e : Error)
    (suffix : State → B → Cut E original State Event Error C) :
    thenDo
      (thenDo (⟨s, before, .returned a⟩ : Cut E original State Event Error A)
        (fun _ _ => (⟨s', childEvents, .rejected e⟩ : Cut E original State Event Error B))) suffix =
      ⟨s', before ++ childEvents, .rejected e⟩ := rfl

#print axioms rejected_short_circuit
#print axioms aborted_short_circuit
#print axioms rejected_cleanup
#print axioms abort_has_no_normal_cleanup
#print axioms mapped_rejection_retains_effects
#print axioms thenDo_associative
#print axioms rejection_queries_retained
#print axioms successful_prefix_then_rejection
end AspisR1.S2D
