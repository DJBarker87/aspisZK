import Aeneas
open Aeneas Aeneas.Std Result
namespace R1Z.PV_DL_CompressionTrace
set_option autoImplicit false

/-- A compression callback is a parameter, including its Result behavior.
No SHA-NI semantics, backend equality, or totality is assumed. -/
def run {S B : Type} (compress : S → B → Result S) : List B → S → Result S
  | [],state => ok state
  | block::tail,state => do
    let next ← compress state block
    run compress tail next

theorem empty {S B : Type} (compress : S → B → Result S) (state : S) :
    run compress [] state=ok state := rfl

theorem append {S B : Type} (compress : S → B → Result S)
    (a b : List B) (state : S) :
    run compress (a++b) state=(do let next ← run compress a state;run compress b next) := by
  induction a generalizing state with
  | nil => simp only [List.nil_append,run,bind_tc_ok]
  | cons block tail ih =>
    simp only [List.cons_append,run,bind_assoc_eq]
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro next hnext
    exact ih next

theorem event_transport {S B : Type} (native reference : List B)
    (events : native=reference) (state : S) :
    ∀ compress : S → B → Result S,
      run compress native state=run compress reference state := by
  intro compress
  rw [events]

/-- Both backend instances follow from event transport independently. -/
theorem backend_instances {S B : Type} (native reference : List B)
    (events : native=reference) (state : S)
    (soft shani : S → B → Result S) :
    run soft native state=run soft reference state ∧
    run shani native state=run shani reference state :=
  ⟨event_transport native reference events state soft,
   event_transport native reference events state shani⟩

#print axioms run
#print axioms empty
#print axioms append
#print axioms event_transport
#print axioms backend_instances
end R1Z.PV_DL_CompressionTrace
