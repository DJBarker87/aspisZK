import R1Z.ProverCommitSemanticSource28
import R1Z.ProverCommitSemantic20
import R1Z.ProverCommitControl28
/-! Bounded monadic lift of the complete retained 25-row loop. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitSemanticRows28
open Aeneas Aeneas.Std Result AspisR1SimSemantic20 ProverCommitStateLift28
abbrev Values := ProverCommitSemantic20.Values
abbrev Records := ProverCommitSemantic20.Records
abbrev State (H : Type) := ProverCommitSemantic20.State H

def rows {M : Type → Type} [Monad M] [MonadLiftT Result M] {H : Type}
    (effect : H → Parts → M Bytes32) (records : Records) (row : Usize) :
    Nat → State H → Values → M ((core.result.Result Values r1_wire.Error) × State H)
  | 0, state, sem => pure (core.result.Result.Ok sem,state)
  | n+1, state, sem => do
    let index ← lift (UScalar.cast .U8 row)
    let value ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (alloc.vec.Vec U8)) records row
    let record ← alloc.vec.CloneVec.clone core.clone.CloneU8 value
    let (value,next) ← ProverCommitSemanticProgram28.semantic effect state index record
    match value with
    | core.result.Result.Err e => pure (core.result.Result.Err e,next)
    | core.result.Result.Ok value => do
      let sem ← Array.update sem row value
      rows effect records (Usize.wrapping_add row 1#usize) n next sem

theorem finite_source {H : Type} (hash : aspis_core.digest.Digest32 H)
    (records : Records) (row : Usize) (n : Nat) (state : State H) (sem : Values) :
    ProverCommitSemantic20.finite hash records row n state sem =
    rows hash.digest records row n state sem := by
  induction n generalizing row state sem with
  | zero => rfl
  | succ n ih =>
    simp only [ProverCommitSemantic20.finite,rows,← ProverCommitSemanticSource28.semantic]
    repeat
      apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro v hv
      try (change (_ × _) at v; rcases v with ⟨v1,v2⟩)
      try dsimp only [Aeneas.Std.uncurry]
    cases v1 with
    | Err e => rfl
    | Ok value =>
      apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro next hn
      exact ih _ _ _

/-- Exact actual extracted loop, under its existing row-count invariant. -/
theorem extracted_source {H : Type} (hash : aspis_core.digest.Digest32 H)
    (records : Records) (row : Usize) (n : Nat) (state : State H) (sem : Values)
    (count : row.val+n=25) :
    r1_wire.semantic20.rows hash state records row sem =
    rows hash.digest records row n state sem := by
  rw [ProverCommitSemantic20.extracted_finite hash records row n state sem count]
  exact finite_source hash records row n state sem

/-- Includes invalid rows/records, partial arrays, and all early inner errors. -/
theorem rows_effects (records : Records) (row : Usize) (n : Nat) (state : State Unit)
    (sem : Values) (machine : ProverCommitCoinCall27.Machine) :
    rows (ProverCommitControl28.dictionary ProverCommitControl28.extracted)
      records row n state sem machine =
    rows (ProverCommitControl28.dictionary ProverCommitControl28.reference)
      records row n state sem machine := by
  exact install _ _ ProverCommitCoinCall27.call_exact
    (fun e => rows (ProverCommitControl28.dictionary e) records row n state sem) machine

#print axioms finite_source
#print axioms extracted_source
#print axioms rows_effects
end R1Z.ProverCommitSemanticRows28
