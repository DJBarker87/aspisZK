import R1Z.ProverCommitStep29
/-! Finite P6 loop composition, with the owned-step error projection explicit. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitRows29
open Aeneas Aeneas.Std Result AspisR1SimSemantic20 ProverCommitStateLift28 ProverCommitStep29

def rows {M : Type → Type} [Monad M] [MonadLiftT Result M] {H : Type}
    (effect : H → Parts → M Bytes32) (records : Records) (row : Usize) :
    Nat → State H → Values → M (Output H)
  | 0, state, sem => pure (.Ok (state,sem))
  | n+1, state, sem => do
    let index ← lift (UScalar.cast .U8 row)
    let record ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (alloc.vec.Vec U8)) records row
    let record ← alloc.vec.CloneVec.clone core.clone.CloneU8 record
    let sample ← iteration effect state index record sem
    match sample with
    | .Err e => pure (.Err e)
    | .Ok (next,sem) => rows effect records (Usize.wrapping_add row 1#usize) n next sem

theorem cast_roundtrip (row : Usize) (bound : row.val<25) :
    UScalar.cast .Usize (UScalar.cast .U8 row) = row := by scalar_tac

theorem bind_same {M : Type → Type} [Monad M] {A B : Type}
    (p : M A) (f g : A → M B) (h : ∀ a, f a = g a) :
    (p >>= f) = (p >>= g) := congrArg (fun k => p >>= k) (funext h)

theorem lift_ok {M : Type → Type} [Monad M] [MonadLiftT Result M]
    [LawfulMonadLiftT Result M] {A : Type} (v : A) :
    (liftM (ok v) : M A) = pure v := by
  change (monadLift (pure v : Result A) : M A) = pure v
  exact monadLift_pure v

/-- All finite prefixes, including malformed records, failures, divergence and
inner semantic errors; local error state is projected away as the native `?` does. -/
theorem rows_model {M : Type → Type} [Monad M] [LawfulMonad M]
    [MonadLiftT Result M] [LawfulMonadLiftT Result M] {H : Type}
    (effect : H → Parts → M Bytes32) (records : Records) (row : Usize)
    (n : Nat) (state : State H) (sem : Values) (count : row.val+n≤25) :
    rows effect records row n state sem =
    (do let result ← ProverCommitSemanticRows28.rows effect records row n state sem
        pure (ProverCommitStep29.discard result)) := by
  induction n generalizing row state sem with
  | zero => simp only [rows,ProverCommitSemanticRows28.rows,pure_bind,ProverCommitStep29.discard]
  | succ n ih =>
    have rt := cast_roundtrip row (by omega)
    simp only [rows,ProverCommitSemanticRows28.rows,iteration,lift,
      lift_ok,pure_bind,bind_assoc,rt]
    apply bind_same
    intro record
    apply bind_same
    intro record
    apply bind_same
    intro result
    rcases result with ⟨value,next⟩
    cases value with
    | Err e => simp only [pure_bind,ProverCommitStep29.discard]
    | Ok value =>
      simp only [bind_assoc,pure_bind]
      apply bind_same
      intro after
      exact ih (Usize.wrapping_add row 1#usize) next after
        (by rw [ProverCommitSemantic20.increment row (by omega)];omega)

/-- The native Range<u8> loop counter; the Nat argument bounds the induction,
not the source execution or the sampler. -/
def rangeRows {M : Type → Type} [Monad M] [MonadLiftT Result M] {H : Type}
    (effect : H → Parts → M Bytes32) (records : Records) (row : U8) :
    Nat → State H → Values → M (Output H)
  | 0, state, sem => pure (.Ok (state,sem))
  | n+1, state, sem => do
    if row < 25#u8 then
      let index ← lift (UScalar.cast .Usize row)
      let record ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (alloc.vec.Vec U8)) records index
      let record ← alloc.vec.CloneVec.clone core.clone.CloneU8 record
      let sample ← iteration effect state row record sem
      match sample with
      | .Err e => pure (.Err e)
      | .Ok (next,sem) => rangeRows effect records (U8.wrapping_add row 1#u8) n next sem
    else pure (.Ok (state,sem))

theorem range_cast (row : U8) :
    UScalar.cast .U8 (UScalar.cast .Usize row) = row := by scalar_tac

theorem range_value (row : U8) (bound : row.val<25) :
    (U8.wrapping_add row 1#u8).val = row.val+1 := by
  rw [U8.wrapping_add_val_eq]
  have one : (1#u8).val=1 := by scalar_tac
  rw [one]
  apply Nat.mod_eq_of_lt
  have cap := (25#u8).hSize
  change 25<UScalar.size .U8 at cap
  omega

theorem range_increment (row : U8) (bound : row.val<25) :
    UScalar.cast .Usize (U8.wrapping_add row 1#u8) =
    Usize.wrapping_add (UScalar.cast .Usize row) 1#usize := by
  have hv := range_value row bound
  have hu := ProverCommitSemantic20.increment (UScalar.cast .Usize row) (by scalar_tac)
  scalar_tac

theorem range_model {M : Type → Type} [Monad M] [LawfulMonad M]
    [MonadLiftT Result M] [LawfulMonadLiftT Result M] {H : Type}
    (effect : H → Parts → M Bytes32) (records : Records) (row : U8)
    (n : Nat) (state : State H) (sem : Values) (count : row.val+n=25) :
    rangeRows effect records row n state sem =
    rows effect records (UScalar.cast .Usize row) n state sem := by
  induction n generalizing row state sem with
  | zero => rfl
  | succ n ih =>
    have bound : row.val<25 := by omega
    have more : row<25#u8 := by scalar_tac
    simp only [rangeRows,rows,more,if_true,lift,lift_ok,pure_bind,range_cast]
    apply bind_same
    intro record
    apply bind_same
    intro record
    apply bind_same
    intro sample
    cases sample with
    | Err e => rfl
    | Ok result =>
      rcases result with ⟨next,after⟩
      change rangeRows effect records (U8.wrapping_add row 1#u8) n next after = _
      rw [ih (U8.wrapping_add row 1#u8) next after (by rw [range_value row bound];omega)]
      rw [range_increment row bound]

#print axioms cast_roundtrip
#print axioms bind_same
#print axioms lift_ok
#print axioms rows_model
#print axioms range_cast
#print axioms range_value
#print axioms range_increment
#print axioms range_model
end R1Z.ProverCommitRows29
