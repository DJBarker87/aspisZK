import S2W_Trace
set_option autoImplicit false
namespace AspisR1.S2W_TraceFacts
open Aeneas Aeneas.Std Result AdapterRw S2W_Trace

def ValidEvent (ops : Ops) : Event → Prop
  | .returned op value => invoke ops op = ok value

theorem success_exists (ops : Ops) {A : Type} (p : Code A) (before : Log)
    (a : A) (success : erase ops p = ok a) :
    ∃ after, run ops p before = ok (a,after) := by
  have eq := erase_run ops p before
  rw [success] at eq
  cases h : run ops p before with
  | fail e => simp only [h,forget,thenResult] at eq; cases eq
  | div => simp only [h,forget,thenResult] at eq; cases eq
  | ok pair =>
    simp only [h,forget,thenResult] at eq
    have same := Result.ok.inj eq
    exact ⟨pair.2, congrArg Result.ok (Prod.ext same rfl)⟩

theorem run_valid (ops : Ops) {A : Type} (p : Code A)
    (before after : Log) (a : A)
    (initial : ∀ e ∈ before, ValidEvent ops e)
    (success : run ops p before = ok (a,after)) :
    ∀ e ∈ after, ValidEvent ops e := by
  induction p generalizing before after with
  | done b =>
    have same := congrArg Prod.snd (Result.ok.inj success)
    change before = after at same
    rw [← same]
    exact initial
  | step r k ih =>
    cases r with
    | fail e => cases success
    | div => cases success
    | ok b => exact ih b before after initial success
  | call op k ih =>
    cases h : invoke ops op with
    | fail e => simp only [run,thenResult,h] at success; cases success
    | div => simp only [run,thenResult,h] at success; cases success
    | ok b =>
      simp only [run,thenResult,h] at success
      apply ih b _ after _ success
      intro event member
      rcases List.mem_append.mp member with old | new
      · exact initial event old
      · have same : event = .returned op b := List.mem_singleton.mp new
        subst event
        exact h

theorem run_bind (ops : Ops) {A B : Type} (p : Code A) (k : A → Code B)
    (log : Log) : run ops (p >>= k) log =
      thenResult (run ops p log) (fun pair => run ops (k pair.1) pair.2) := by
  induction p generalizing log with
  | done a => rfl
  | step r c ih =>
    change thenResult r (fun b => run ops (S2W_Trace.bind (c b) k) log) = _
    have h : ∀ b log, run ops (S2W_Trace.bind (c b) k) log =
      thenResult (run ops (c b) log) (fun pair => run ops (k pair.1) pair.2) := ih
    simp only [h,run]
    cases r <;> rfl
  | call op c ih =>
    change thenResult (invoke ops op)
      (fun b => run ops (S2W_Trace.bind (c b) k) (log ++ [.returned op b])) = _
    have h : ∀ b log, run ops (S2W_Trace.bind (c b) k) log =
      thenResult (run ops (c b) log) (fun pair => run ops (k pair.1) pair.2) := ih
    simp only [h,run]
    cases invoke ops op <;> rfl

#print axioms success_exists
#print axioms run_valid
#print axioms run_bind
end AspisR1.S2W_TraceFacts
