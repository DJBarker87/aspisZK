import FSTranscriptScript

set_option autoImplicit false
set_option Elab.async false
namespace AspisV8Completion.S8RunLevelBind
open FSOracleExecution FSBoundedTranscript FSTranscriptScript
abbrev Bytes := List UInt8
variable {A B C : Type} {n m k : Nat}

theorem successful_bind_split (tape : Tape)
    (p : Script Bytes Block A n) (next : A → Script Bytes Block B m)
    (initial final : Oracle) (value : B)
    (h : run tape (bind p next) initial = (some value, final)) :
    ∃ a middle, run tape p initial = (some a, middle) ∧
      run tape (next a) middle = (some value, final) := by
  rw [run_bind] at h
  cases hp : run tape p initial with
  | mk result middle =>
    cases result with
    | none => simp only [hp] at h; cases h
    | some a => exact ⟨a, middle, rfl, by simpa only [hp] using h⟩

theorem run_bind_associative (tape : Tape)
    (p : Script Bytes Block A n) (f : A → Script Bytes Block B m)
    (g : B → Script Bytes Block C k) (s : Oracle) :
    run tape (bind (bind p f) g) s =
      run tape (bind p (fun a => bind (f a) g)) s := by
  rw [run_bind, run_bind]
  cases hp : run tape p s with
  | mk result middle =>
    cases result with
    | none => simp only [run_bind, hp]
    | some a => simp only [run_bind, hp]

theorem run_bind_congr (tape : Tape)
    (p : Script Bytes Block A n)
    (f : A → Script Bytes Block B m) (g : A → Script Bytes Block B k)
    (pointwise : ∀ a s, run tape (f a) s = run tape (g a) s)
    (initial : Oracle) :
    run tape (bind p f) initial = run tape (bind p g) initial := by
  rw [run_bind, run_bind]
  cases h : (run tape p initial).1 with
  | none => rfl
  | some a => exact pointwise a _

#print axioms successful_bind_split
#print axioms run_bind_associative
#print axioms run_bind_congr
end AspisV8Completion.S8RunLevelBind
