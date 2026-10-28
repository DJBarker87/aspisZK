import AspisR1SimulatorInsert19.Funs
set_option autoImplicit false
namespace R1Z.ProverCommitSimulatorInsert19
open Aeneas Aeneas.Std Result AspisR1SimulatorInsert19
abbrev Bytes := alloc.vec.Vec U8
abbrev Answer := Array U8 32#usize
abbrev Entry := Bytes × Answer
abbrev Table := alloc.vec.Vec Entry

def finite (table : Table) (index : Usize) (address : Bytes) (answer : Answer)
    (collision : Bool) : Nat → Result (Table × Bool)
  | 0 => do
    let after ← alloc.vec.Vec.push table (address,answer)
    ok (after,collision)
  | remaining+1 => do
    let pair ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Entry) table index
    let (key,previous) ← (BuiltinClone Entry).clone pair
    let same ← alloc.vec.partial_eq.PartialEqVec.eq core.cmp.PartialEqU8 key address
    if same then
      let (_,back) ← alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice Entry) table index
      let after := back (key,answer)
      if collision then ok (after,true) else do
        let conflict ← core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 previous answer
        ok (after,conflict)
    else finite table (Usize.wrapping_add index 1#usize) address answer collision remaining

theorem increment (table : Table) (index : Usize) (bound : index.val < table.length) :
    (Usize.wrapping_add index 1#usize).val = index.val+1 := by
  rw [Usize.wrapping_add_val_eq]
  have one : (1#usize).val = 1 := by scalar_tac
  rw [one]
  have hsize := (alloc.vec.Vec.len table).hSize
  simp only [alloc.vec.Vec.len_val] at hsize
  exact Nat.mod_eq_of_lt (by omega)

/-- Exact finite reference schedule, retaining overwrite conflicts, original
sticky collision state, all scalar/byte errors and partially retained tables. -/
theorem extracted_finite (table : Table) (index : Usize) (address : Bytes)
    (answer : Answer) (collision : Bool) (remaining : Nat)
    (count : index.val+remaining = table.length) :
    sim.owned19.insert table index address answer collision =
      finite table index address answer collision remaining := by
  induction remaining generalizing index with
  | zero =>
    have stop : index = alloc.vec.Vec.len table := by scalar_tac
    rw [sim.owned19.insert]
    simp only [stop,if_true,finite]
  | succ n ih =>
    have more : index ≠ alloc.vec.Vec.len table := by scalar_tac
    rw [sim.owned19.insert]
    simp only [more,if_false,finite]
    cases hp : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Entry) table index with
    | fail e => simp only [bind_tc_fail]
    | div => simp only [bind_tc_div]
    | ok pair =>
      simp only [bind_tc_ok]
      cases hc : (BuiltinClone Entry).clone pair with
      | fail e => simp only [bind_tc_fail]
      | div => simp only [bind_tc_div]
      | ok pair =>
        rcases pair with ⟨key,previous⟩
        simp only [bind_tc_ok,Aeneas.Std.uncurry_apply_pair]
        cases he : alloc.vec.partial_eq.PartialEqVec.eq core.cmp.PartialEqU8 key address with
        | fail e => simp only [bind_tc_fail]
        | div => simp only [bind_tc_div]
        | ok same =>
          simp only [bind_tc_ok]
          cases same with
          | true => rfl
          | false =>
            simp only [Bool.false_eq_true,if_false,lift,bind_tc_ok]
            exact ih (Usize.wrapping_add index 1#usize)
              (by rw [increment table index (by omega)]; omega)

#print axioms increment
#print axioms extracted_finite
#print axioms AspisR1SimulatorInsert19.sim.owned19.insert
end R1Z.ProverCommitSimulatorInsert19
