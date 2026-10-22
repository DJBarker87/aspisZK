import AspisR1SimulatorConcat19.Funs
set_option autoImplicit false
namespace R1Z.ProverCommitSimulatorConcat19
open Aeneas Aeneas.Std Result AspisR1SimulatorConcat19
abbrev Bytes := alloc.vec.Vec U8
abbrev Parts := alloc.vec.Vec Bytes

def finite (parts : Parts) (index : Usize) : Nat → Bytes → Result Bytes
  | 0, output => ok output
  | n+1, output => do
    let value ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Bytes) parts index
    let part ← alloc.vec.CloneVec.clone core.clone.CloneU8 value
    let after ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 output (alloc.vec.Vec.deref part)
    finite parts (Usize.wrapping_add index 1#usize) n after

theorem increment (parts : Parts) (index : Usize) (bound : index.val < parts.length) :
    (Usize.wrapping_add index 1#usize).val = index.val+1 := by
  rw [Usize.wrapping_add_val_eq]
  have one : (1#usize).val = 1 := by scalar_tac
  rw [one]
  have hsize := (alloc.vec.Vec.len parts).hSize
  simp only [alloc.vec.Vec.len_val] at hsize
  exact Nat.mod_eq_of_lt (by omega)

/-- The recursive extracted Rust reference is equal to a finite schedule on
its admitted index range. Index/clone/append errors and divergence are retained;
this is not just equality of successful bytes. -/
theorem extracted_finite (parts : Parts) (index : Usize) (remaining : Nat) (output : Bytes)
    (count : index.val+remaining = parts.length) :
    sim.owned19.concat parts index output = finite parts index remaining output := by
  induction remaining generalizing index output with
  | zero =>
    have stop : index = alloc.vec.Vec.len parts := by scalar_tac
    rw [sim.owned19.concat]
    simp only [stop, if_true,finite]
  | succ n ih =>
    have more : index ≠ alloc.vec.Vec.len parts := by scalar_tac
    rw [sim.owned19.concat]
    simp only [more, if_false,finite]
    cases hg : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Bytes) parts index with
    | fail e => simp only [hg, bind_tc_fail]
    | div => simp only [hg, bind_tc_div]
    | ok value =>
      simp only [hg,bind_tc_ok]
      cases hc : alloc.vec.CloneVec.clone core.clone.CloneU8 value with
      | fail e => simp only [hc,bind_tc_fail]
      | div => simp only [hc,bind_tc_div]
      | ok part =>
        simp only [hc,bind_tc_ok]
        cases ha : alloc.vec.Vec.extend_from_slice core.clone.CloneU8 output (alloc.vec.Vec.deref part) with
        | fail e => simp only [ha,bind_tc_fail]
        | div => simp only [ha,bind_tc_div]
        | ok after =>
          simp only [ha,bind_tc_ok,lift]
          exact ih (Usize.wrapping_add index 1#usize) after
            (by rw [increment parts index (by omega)]; omega)

#print axioms increment
#print axioms extracted_finite
#print axioms AspisR1SimulatorConcat19.sim.owned19.concat
end R1Z.ProverCommitSimulatorConcat19
