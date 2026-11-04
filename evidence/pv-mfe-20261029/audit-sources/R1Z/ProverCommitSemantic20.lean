import AspisR1SimSemantic20.Funs
set_option autoImplicit false
namespace R1Z.ProverCommitSemantic20
open Aeneas Aeneas.Std Result AspisR1SimSemantic20
abbrev Bytes := alloc.vec.Vec U8
abbrev Records := alloc.vec.Vec Bytes
abbrev Values := Array aspis_core.field.QM31 25#usize
abbrev State (H : Type) := r1_wire.SemanticTranscript H
abbrev Outcome (H : Type) := Result ((core.result.Result Values r1_wire.Error) × State H)

def finite {H : Type} (hash : aspis_core.digest.Digest32 H) (records : Records)
    (row : Usize) : Nat → State H → Values → Result ((core.result.Result Values r1_wire.Error) × State H)
  | 0, state, sem => ok (core.result.Result.Ok sem,state)
  | n+1, state, sem => do
    let index ← lift (UScalar.cast .U8 row)
    let value ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Bytes) records row
    let record ← alloc.vec.CloneVec.clone core.clone.CloneU8 value
    let (value,next) ← r1_wire.semantic20.semantic hash state index record
    match value with
    | core.result.Result.Err e => ok (core.result.Result.Err e,next)
    | core.result.Result.Ok value => do
      let sem ← Array.update sem row value
      finite hash records (Usize.wrapping_add row 1#usize) n next sem

theorem increment (row : Usize) (bound : row.val<25) :
    (Usize.wrapping_add row 1#usize).val=row.val+1 := by
  rw [Usize.wrapping_add_val_eq]
  have one : (1#usize).val=1 := by scalar_tac
  rw [one]
  apply Nat.mod_eq_of_lt
  have cap := (25#usize).hSize
  change 25<UScalar.size .Usize at cap
  omega

/-- Full finite semantic-row execution including errors, advanced state,
array updates, cloned bytes and the actual three-read hash interface. -/
theorem extracted_finite {H : Type} (hash : aspis_core.digest.Digest32 H)
    (records : Records) (row : Usize) (remaining : Nat) (state : State H) (sem : Values)
    (count : row.val+remaining=25) :
    r1_wire.semantic20.rows hash state records row sem =
      finite hash records row remaining state sem := by
  induction remaining generalizing row state sem with
  | zero =>
    have stop : row=25#usize := by scalar_tac
    rw [r1_wire.semantic20.rows]
    simp only [stop,if_true,finite]
  | succ n ih =>
    have more : row≠25#usize := by scalar_tac
    rw [r1_wire.semantic20.rows]
    simp only [more,if_false,finite,lift,bind_tc_ok]
    cases hi : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Bytes) records row with
    | fail e => simp only [bind_tc_fail]
    | div => simp only [bind_tc_div]
    | ok value =>
      simp only [bind_tc_ok]
      cases hc : alloc.vec.CloneVec.clone core.clone.CloneU8 value with
      | fail e => simp only [bind_tc_fail]
      | div => simp only [bind_tc_div]
      | ok record =>
        simp only [bind_tc_ok]
        cases hs : r1_wire.semantic20.semantic hash state (UScalar.cast .U8 row) record with
        | fail e => simp only [bind_tc_fail]
        | div => simp only [bind_tc_div]
        | ok result =>
          rcases result with ⟨value,next⟩
          simp only [bind_tc_ok,Aeneas.Std.uncurry_apply_pair]
          cases value with
          | Err e => rfl
          | Ok value =>
            cases hu : Array.update sem row value with
            | fail e => simp only [hu,bind_tc_fail]
            | div => simp only [hu,bind_tc_div]
            | ok after =>
              simp only [hu,bind_tc_ok,lift]
              exact ih (Usize.wrapping_add row 1#usize) next after
                (by rw [increment row (by omega)];omega)

#print axioms increment
#print axioms extracted_finite
#print axioms AspisR1SimSemantic20.r1_wire.semantic20.rows
#print axioms AspisR1SimSemantic20.r1_wire.semantic20.semantic
#print axioms AspisR1SimSemantic20.r1_wire.fields20.validate
end R1Z.ProverCommitSemantic20
