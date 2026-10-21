import R1Z.ProverCommitShippedSchedule

/-! Composition of per-call-site next-word contracts over the fixed scalar
schedule. The explicit step law is the interface for the Kani certificate;
this file does not manufacture its concrete whole-Rust instance. -/
set_option autoImplicit false
namespace R1Z.ProverCommitShippedTransport
open Aeneas Aeneas.Std Result
open ProverCommitShippedSchedule
variable {A B : Type}

def mapFinite (f : A → B) (r : Result (A × Option Sample)) :
    Result (B × Option Sample) := do
  let (s, pending) ← r
  ok (f s, pending)

def mapScalar (f : A → B) (r : Result (Sample × A)) : Result (Sample × B) := do
  let (sample, s) ← r
  ok (sample, f s)

theorem finite_transport (left : A → Result (U32 × A))
    (right : B → Result (U32 × B)) (f : A → B)
    (step : ∀ s, (do let (word, after) ← left s; ok (word, f after)) = right (f s))
    (n : Nat) (s : A) :
    mapFinite f (mask.finite left n s) = mask.finite right n (f s) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    rw [mask.finite, mask.finite, ← step]
    cases hn : left s with
    | fail error => rfl
    | div => rfl
    | ok pair =>
      rcases pair with ⟨word, after⟩
      simp only [mapFinite, bind_tc_ok, Aeneas.Std.uncurry_apply_pair, lift]
      split_ifs
      · rfl
      · exact ih after

theorem source_finite_eq (nextWord : A → Result (U32 × A)) (n : Nat) (s : A) :
    source.finite nextWord n s = mask.finite nextWord n s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [source.finite, mask.finite]
    congr 1
    funext pair
    rcases pair with ⟨word, after⟩
    simp only [Aeneas.Std.uncurry_apply_pair, lift, bind_tc_ok]
    split_ifs
    · rfl
    · exact ih after

theorem mask_scalar_transport (left : A → Result (U32 × A))
    (right : B → Result (U32 × B)) (f : A → B)
    (step : ∀ s, (do let (word, after) ← left s; ok (word, f after)) = right (f s))
    (s : A) :
    mapScalar f (mask.scalar left s) = mask.scalar right (f s) := by
  unfold mapScalar
  rw [mask.scalar_sixteen, mask.scalar_sixteen,
    ← finite_transport left right f step 16 s]
  simp only [mapFinite, bind_assoc_eq]
  congr 1
  funext pair
  rcases pair with ⟨after, pending⟩
  cases pending <;> rfl

theorem source_scalar_transport (left : A → Result (U32 × A))
    (right : B → Result (U32 × B)) (f : A → B)
    (step : ∀ s, (do let (word, after) ← left s; ok (word, f after)) = right (f s))
    (s : A) :
    mapScalar f (source.scalar left s) = source.scalar right (f s) := by
  unfold mapScalar
  rw [source.scalar_sixteen, source.scalar_sixteen,
    source_finite_eq, source_finite_eq,
    ← finite_transport left right f step 16 s]
  simp only [mapFinite, bind_assoc_eq]
  congr 1
  funext pair
  rcases pair with ⟨after, pending⟩
  cases pending <;> rfl

#print axioms finite_transport
#print axioms source_finite_eq
#print axioms mask_scalar_transport
#print axioms source_scalar_transport
end R1Z.ProverCommitShippedTransport
