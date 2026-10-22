import R1Z.ProverCommitKeyCompare21
/-! Universal comparator transport in the actual extracted owned table loop.
Clone, indexing, update, byte-array comparison and Vec growth remain intact.
This does not identify that owned loop with Rust std::BTreeMap insertion. -/
set_option autoImplicit false
namespace R1Z.ProverCommitTableKeys21
open Aeneas Aeneas.Std Result ProverCommitSimulatorInsert19

def finite (table : Table) (index : Usize) (address : Bytes) (answer : Answer)
    (collision : Bool) : Nat → Result (Table × Bool)
  | 0 => do
    let after ← alloc.vec.Vec.push table (address,answer)
    ok (after,collision)
  | remaining+1 => do
    let pair ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Entry) table index
    let (key,previous) ← (BuiltinClone Entry).clone pair
    if key.val=address.val then
      let (_,back) ← alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice Entry) table index
      let after := back (key,answer)
      if collision then ok (after,true) else do
        let conflict ← core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 previous answer
        ok (after,conflict)
    else finite table (Usize.wrapping_add index 1#usize) address answer collision remaining

theorem finite_keys (table : Table) (index : Usize) (address : Bytes) (answer : Answer)
    (collision : Bool) (remaining : Nat) :
    ProverCommitSimulatorInsert19.finite table index address answer collision remaining =
      finite table index address answer collision remaining := by
  induction remaining generalizing index with
  | zero => rfl
  | succ n ih =>
    simp only [ProverCommitSimulatorInsert19.finite,finite]
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
        simp only [bind_tc_ok,Aeneas.Std.uncurry_apply_pair,ProverCommitKeyCompare21.vec_eq]
        simp only [bind_tc_ok,decide_eq_true_eq]
        split
        · rfl
        · exact ih _

/-- All finite table lengths and byte-key lengths, not a fixed unwind bound. -/
theorem extracted_keys (table : Table) (index : Usize) (address : Bytes) (answer : Answer)
    (collision : Bool) (remaining : Nat) (count : index.val+remaining=table.length) :
    AspisR1SimulatorInsert19.sim.owned19.insert table index address answer collision =
      finite table index address answer collision remaining := by
  rw [ProverCommitSimulatorInsert19.extracted_finite table index address answer collision remaining count]
  exact finite_keys table index address answer collision remaining

#print axioms finite_keys
#print axioms extracted_keys
end R1Z.ProverCommitTableKeys21
