import AspisR1ProverBalance9.Funs
import R1Z.ProverCommitFoldSteps

/-! The complete extracted owned balancing recursion equals a finite ascending
fold, including all indexing and arithmetic errors. No concrete 1024-row
normalization is used. Kani checks the shipped filter/fold row transition. -/
set_option autoImplicit false
namespace R1Z.ProverCommitBalanceRecursion
open Aeneas Aeneas.Std Result AspisR1ProverBalance9
open R1Z.ProverCommitFoldSteps (foldSteps)

def rowSequence : Nat → Usize → List Usize
  | 0, _ => []
  | n+1, row => row :: rowSequence n (Usize.wrapping_add row 1#usize)

theorem next_row (row : Usize) (h : row.val < 1024) :
    (Usize.wrapping_add row 1#usize).val = row.val + 1 := by
  rw [Usize.wrapping_add_val_eq]
  apply Nat.mod_eq_of_lt
  have bound : 2^32 ≤ UScalar.size .Usize := by
    rw [UScalar.size_def]
    exact Nat.pow_le_pow_right (by decide) System.Platform.le_numBits
  have one : (1#usize).val = 1 := by scalar_tac
  rw [one]
  omega

theorem sequence_ascending (n : Nat) (row : Usize)
    (remaining : row.val + n = 1024) :
    (rowSequence n row).map (fun r => r.val) = List.range' row.val n := by
  induction n generalizing row with
  | zero => rfl
  | succ n ih =>
    have hr : row.val < 1024 := by omega
    simp only [rowSequence, List.map_cons, List.range'_succ]
    rw [ih _ (by rw [next_row row hr]; omega), next_row row hr]

def m31ReadStep (table : Slice aspis_core.field.M31) (dependent : Usize)
    (active : Aeneas.Std.Array Bool 1024#usize) (row : Usize)
    (sum : aspis_core.field.M31) : Result aspis_core.field.M31 := do
  let value ← Slice.index_usize table row
  let selected ← Aeneas.Std.Array.index_usize active row
  prover_commit_reference.balance_m31_step sum value selected row dependent

def qm31ReadStep (table : Slice aspis_core.field.QM31) (dependent : Usize)
    (active : Aeneas.Std.Array Bool 1024#usize) (row : Usize)
    (sum : aspis_core.field.QM31) : Result aspis_core.field.QM31 := do
  let value ← Slice.index_usize table row
  let selected ← Aeneas.Std.Array.index_usize active row
  prover_commit_reference.balance_qm31_step sum value selected row dependent

theorem m31_rows_fold (table : Slice aspis_core.field.M31) (dependent : Usize)
    (active : Aeneas.Std.Array Bool 1024#usize) (n : Nat) (row : Usize)
    (sum : aspis_core.field.M31) (remaining : row.val + n = 1024) :
    prover_commit_reference.balance_m31_rows table dependent active row sum =
      foldSteps (m31ReadStep table dependent active) (rowSequence n row) sum := by
  induction n generalizing row sum with
  | zero =>
    have stopped : ¬ row < 1024#usize := by scalar_tac
    rw [prover_commit_reference.balance_m31_rows]
    simp only [stopped, if_false, rowSequence, foldSteps]
  | succ n ih =>
    have running : row < 1024#usize := by scalar_tac
    have hr : row.val < 1024 := by omega
    rw [prover_commit_reference.balance_m31_rows]
    simp only [running, if_true, rowSequence, foldSteps, m31ReadStep, bind_assoc_eq]
    cases hv : Slice.index_usize table row with
    | fail e => rfl
    | div => rfl
    | ok value =>
      simp only [bind_tc_ok]
      cases ha : Aeneas.Std.Array.index_usize active row with
      | fail e => rfl
      | div => rfl
      | ok selected =>
        simp only [bind_tc_ok]
        cases hs : prover_commit_reference.balance_m31_step sum value selected row dependent with
        | fail e => rfl
        | div => rfl
        | ok after =>
          simp only [bind_tc_ok, lift]
          exact ih _ after (by rw [next_row row hr]; omega)

theorem m31_all_rows (table : Slice aspis_core.field.M31) (dependent : Usize)
    (active : Aeneas.Std.Array Bool 1024#usize) (sum : aspis_core.field.M31) :
    prover_commit_reference.balance_m31_rows table dependent active 0#usize sum =
      foldSteps (m31ReadStep table dependent active) (rowSequence 1024 0#usize) sum :=
  m31_rows_fold table dependent active 1024 0#usize sum (by decide)

theorem qm31_rows_fold (table : Slice aspis_core.field.QM31) (dependent : Usize)
    (active : Aeneas.Std.Array Bool 1024#usize) (n : Nat) (row : Usize)
    (sum : aspis_core.field.QM31) (remaining : row.val + n = 1024) :
    prover_commit_reference.balance_qm31_rows table dependent active row sum =
      foldSteps (qm31ReadStep table dependent active) (rowSequence n row) sum := by
  induction n generalizing row sum with
  | zero =>
    have stopped : ¬ row < 1024#usize := by scalar_tac
    rw [prover_commit_reference.balance_qm31_rows]
    simp only [stopped, if_false, rowSequence, foldSteps]
  | succ n ih =>
    have running : row < 1024#usize := by scalar_tac
    have hr : row.val < 1024 := by omega
    rw [prover_commit_reference.balance_qm31_rows]
    simp only [running, if_true, rowSequence, foldSteps, qm31ReadStep, bind_assoc_eq]
    cases hv : Slice.index_usize table row with
    | fail e => rfl
    | div => rfl
    | ok value =>
      simp only [bind_tc_ok]
      cases ha : Aeneas.Std.Array.index_usize active row with
      | fail e => rfl
      | div => rfl
      | ok selected =>
        simp only [bind_tc_ok]
        cases hs : prover_commit_reference.balance_qm31_step sum value selected row dependent with
        | fail e => rfl
        | div => rfl
        | ok after =>
          simp only [bind_tc_ok, lift]
          exact ih _ after (by rw [next_row row hr]; omega)

theorem qm31_all_rows (table : Slice aspis_core.field.QM31) (dependent : Usize)
    (active : Aeneas.Std.Array Bool 1024#usize) (sum : aspis_core.field.QM31) :
    prover_commit_reference.balance_qm31_rows table dependent active 0#usize sum =
      foldSteps (qm31ReadStep table dependent active) (rowSequence 1024 0#usize) sum :=
  qm31_rows_fold table dependent active 1024 0#usize sum (by decide)

/-- Whole owned caller, with the recursive traversal replaced by its proved
ascending fold. Shape errors and the final dependent-cell assignment are exact. -/
theorem m31_owned_fold (table : alloc.vec.Vec aspis_core.field.M31)
    (dependent : Usize) (active : Aeneas.Std.Array Bool 1024#usize) :
    prover_commit_reference.balance_m31_owned table dependent active = (do
      if alloc.vec.Vec.len table != 1024#usize then
        ok (.Err .TraceShape, table)
      else
        let b ← Aeneas.Std.Array.index_usize active dependent
        if b then ok (.Err .TraceShape, table)
        else
          let sum ← foldSteps (m31ReadStep (alloc.vec.Vec.deref table) dependent active)
            (rowSequence 1024 0#usize) aspis_core.field.M31.ZERO
          let value ← aspis_core.field.M31.sub aspis_core.field.M31.ZERO sum
          let (_, back) ← alloc.vec.Vec.index_mut
            (core.slice.index.SliceIndexUsizeSlice aspis_core.field.M31) table dependent
          ok (.Ok (), back value)) := by
  simp only [prover_commit_reference.balance_m31_owned, m31_all_rows]

/-- Whole owned caller, with the recursive traversal replaced by its proved
ascending fold. Shape errors and the final dependent-cell assignment are exact. -/
theorem qm31_owned_fold (table : alloc.vec.Vec aspis_core.field.QM31)
    (dependent : Usize) (active : Aeneas.Std.Array Bool 1024#usize) :
    prover_commit_reference.balance_qm31_owned table dependent active = (do
      if alloc.vec.Vec.len table != 1024#usize then
        ok (.Err .TraceShape, table)
      else
        let b ← Aeneas.Std.Array.index_usize active dependent
        if b then ok (.Err .TraceShape, table)
        else
          let sum ← foldSteps (qm31ReadStep (alloc.vec.Vec.deref table) dependent active)
            (rowSequence 1024 0#usize) aspis_core.field.QM31.ZERO
          let value ← aspis_core.field.QM31.sub aspis_core.field.QM31.ZERO sum
          let (_, back) ← alloc.vec.Vec.index_mut
            (core.slice.index.SliceIndexUsizeSlice aspis_core.field.QM31) table dependent
          ok (.Ok (), back value)) := by
  simp only [prover_commit_reference.balance_qm31_owned, qm31_all_rows]

#print axioms m31_owned_fold
#print axioms qm31_owned_fold
#print axioms next_row
#print axioms sequence_ascending
#print axioms m31_rows_fold
#print axioms m31_all_rows
#print axioms qm31_rows_fold
#print axioms qm31_all_rows
end R1Z.ProverCommitBalanceRecursion
