import AspisR1ProverMaterial14.Funs
set_option autoImplicit false
namespace R1Z.ProverCommitMaterialRecursion
open Aeneas Aeneas.Std Result AspisR1ProverMaterial14
abbrev State := prover_commit_reference.State
abbrev Hash := Slice (Slice U8) → Result (Aeneas.Std.Array U8 32#usize)
abbrev Status := core.result.Result Unit state_only_hiding.StateOnlyMaskBuildError
abbrev Values := alloc.vec.Vec U32

def finite (hash : Hash) (domain : Slice U8) : Nat → Values → State →
    Result (Status × Values × State)
  | 0, values, state => ok (.Ok (), values, state)
  | n+1, values, state => do
    let (sample, after) ← prover_commit_reference.limb_caller hash domain state
    match sample with
    | .Err error => ok (.Err error, values, after)
    | .Ok value =>
      let values' ← alloc.vec.Vec.push values value
      finite hash domain n values' after

theorem sub_one (remaining : Usize) (positive : 0 < remaining.val) :
    (Usize.wrapping_sub remaining 1#usize).val = remaining.val - 1 := by
  rw [Usize.wrapping_sub_val_eq]
  have one : (1#usize).val = 1 := by scalar_tac
  rw [one]
  have hb := remaining.hSize
  have hp : 0 < UScalar.size .Usize := by rw [UScalar.size_def]; positivity
  have he : remaining.val + (UScalar.size .Usize - 1) =
      (remaining.val - 1) + UScalar.size .Usize := by omega
  rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

/-- Exact recursion theorem for the newly extracted owned raw producer.
All allocation failures and partially filled error states are preserved. -/
theorem extracted_finite (hash : Hash) (domain : Slice U8) (n : Nat)
    (remaining : Usize) (values : Values) (state : State) (count : remaining.val = n) :
    prover_commit_reference.collect_m31_owned hash domain state remaining values =
      finite hash domain n values state := by
  induction n generalizing remaining values state with
  | zero =>
    have stop : remaining = 0#usize := by scalar_tac
    rw [prover_commit_reference.collect_m31_owned]
    simp only [stop, if_true, finite]
  | succ n ih =>
    have more : remaining ≠ 0#usize := by scalar_tac
    rw [prover_commit_reference.collect_m31_owned]
    simp only [more, if_false, finite]
    cases hs : prover_commit_reference.limb_caller hash domain state with
    | fail e => rfl
    | div => rfl
    | ok pair =>
      rcases pair with ⟨sample, after⟩
      simp only [bind_tc_ok, Aeneas.Std.uncurry_apply_pair]
      cases sample with
      | Err e => rfl
      | Ok value =>
        dsimp only
        cases hp : alloc.vec.Vec.push values value with
        | fail e => simp only [hp, bind_tc_fail]
        | div => simp only [hp, bind_tc_div]
        | ok values' =>
          simp only [hp, bind_tc_ok, lift]
          exact ih (Usize.wrapping_sub remaining 1#usize) values' after
            (by rw [sub_one remaining (by omega), count]; omega)


abbrev QValues := alloc.vec.Vec aspis_core.field.QM31
def qmFinite (hash : Hash) (domain : Slice U8) : Nat → QValues → State →
    Result (Status × QValues × State)
  | 0, values, state => ok (.Ok (), values, state)
  | n+1, values, state => do
    let (sample, after) ← prover_commit_reference.qm31_caller hash domain state
    match sample with
    | .Err error => ok (.Err error, values, after)
    | .Ok value =>
      let values' ← alloc.vec.Vec.push values value
      qmFinite hash domain n values' after

/-- Exact recursion theorem for the newly extracted owned raw producer.
All allocation failures and partially filled error states are preserved. -/
theorem qm_extracted_finite (hash : Hash) (domain : Slice U8) (n : Nat)
    (remaining : Usize) (values : QValues) (state : State) (count : remaining.val = n) :
    prover_commit_reference.collect_qm31_owned hash domain state remaining values =
      qmFinite hash domain n values state := by
  induction n generalizing remaining values state with
  | zero =>
    have stop : remaining = 0#usize := by scalar_tac
    rw [prover_commit_reference.collect_qm31_owned]
    simp only [stop, if_true, qmFinite]
  | succ n ih =>
    have more : remaining ≠ 0#usize := by scalar_tac
    rw [prover_commit_reference.collect_qm31_owned]
    simp only [more, if_false, qmFinite]
    cases hs : prover_commit_reference.qm31_caller hash domain state with
    | fail e => rfl
    | div => rfl
    | ok pair =>
      rcases pair with ⟨sample, after⟩
      simp only [bind_tc_ok, Aeneas.Std.uncurry_apply_pair]
      cases sample with
      | Err e => rfl
      | Ok value =>
        dsimp only
        cases hp : alloc.vec.Vec.push values value with
        | fail e => simp only [hp, bind_tc_fail]
        | div => simp only [hp, bind_tc_div]
        | ok values' =>
          simp only [hp, bind_tc_ok, lift]
          exact ih (Usize.wrapping_sub remaining 1#usize) values' after
            (by rw [sub_one remaining (by omega), count]; omega)


def columnsFinite
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (domain : Slice Std.U8) (state : prover_commit_reference.State)
  (columns : alloc.vec.Vec (alloc.vec.Vec aspis_core.field.M31))
  (index : Std.Usize) (remaining : Nat) (dependent : Std.Usize)
  (active : Array Bool 1024#usize) :
  Result ((core.result.Result Unit state_only_hiding.StateOnlyMaskBuildError)
    × (alloc.vec.Vec (alloc.vec.Vec aspis_core.field.M31)) ×
    prover_commit_reference.State)
  := do
  if remaining = 0
  then ok (core.result.Result.Ok (), columns, state)
  else
    let v ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (alloc.vec.Vec
        aspis_core.field.M31)) columns index
    let v1 ←
      alloc.vec.CloneVec.clone aspis_core.field.M31.Insts.CoreCloneClone v
    let (result, column, state1) ←
      prover_commit_reference.collect_m31_owned hash domain state 1024#usize v1
    let (_, index_mut_back) ←
      alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice
        (alloc.vec.Vec aspis_core.field.M31)) columns index
    let columns1 := index_mut_back column
    match result with
    | core.result.Result.Ok _ =>
      let v2 ←
        alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
          (alloc.vec.Vec aspis_core.field.M31)) columns1 index
      let v3 ←
        alloc.vec.CloneVec.clone aspis_core.field.M31.Insts.CoreCloneClone v2
      let (result1, column1) ←
        prover_commit_reference.balance_m31_owned v3 dependent active
      let (_, index_mut_back1) ←
        alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice
          (alloc.vec.Vec aspis_core.field.M31)) columns1 index
      let columns2 := index_mut_back1 column1
      match result1 with
      | core.result.Result.Ok _ =>
        let i ← lift (Std.Usize.wrapping_add index 1#usize)
        let i1 := remaining - 1
        columnsFinite hash domain state1
          columns2 i i1 dependent active
      | core.result.Result.Err _ => ok (result1, columns2, state1)
    | core.result.Result.Err _ => ok (result, columns1, state1)
termination_by remaining
decreasing_by omega


/-- The indexed column producer is its finite ascending schedule, preserving
all scalar, allocation, indexing and balancing failures and retained state. -/
theorem columns_extracted_finite (hash : Hash) (domain : Slice U8) (n : Nat)
    (remaining index dependent : Usize) (columns : alloc.vec.Vec (alloc.vec.Vec U32))
    (active : Aeneas.Std.Array Bool 1024#usize) (state : State)
    (count : remaining.val = n) :
    prover_commit_reference.material_columns_owned hash domain state columns index remaining dependent active =
      columnsFinite hash domain state columns index n dependent active := by
  induction n generalizing remaining index columns state with
  | zero =>
    have stop : remaining = 0#usize := by scalar_tac
    rw [prover_commit_reference.material_columns_owned, columnsFinite]
    simp only [stop, if_true]
  | succ n ih =>
    have more : remaining ≠ 0#usize := by scalar_tac
    have next : (Usize.wrapping_sub remaining 1#usize).val = n := by
      rw [sub_one remaining (by omega), count]; omega
    have ih' := fun state columns index => ih
      (Usize.wrapping_sub remaining 1#usize) index columns state next
    rw [prover_commit_reference.material_columns_owned, columnsFinite]
    simp only [more, if_false, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
      Nat.add_sub_cancel, lift, bind_tc_ok, ih']
    rfl

def paddingFinite
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (domain : Slice Std.U8) (state : prover_commit_reference.State)
  (values : alloc.vec.Vec aspis_core.field.QM31) (row : Std.Usize) (remaining : Nat)
  (dependent : Std.Usize) (active : Array Bool 1024#usize) :
  Result ((core.result.Result Unit state_only_hiding.StateOnlyMaskBuildError)
    × (alloc.vec.Vec aspis_core.field.QM31) × prover_commit_reference.State)
  := do
  if remaining = 0
  then ok (core.result.Result.Ok (), values, state)
  else
    let b ← Array.index_usize active row
    if b
    then
      let i ← lift (Std.Usize.wrapping_add row 1#usize)
      paddingFinite hash domain state values i (remaining-1)
        dependent active
    else
      if row != dependent
      then
        let (sample, state1) ←
          prover_commit_reference.qm31_caller hash domain state
        match sample with
        | core.result.Result.Ok value =>
          let (_, index_mut_back) ←
            alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice
              aspis_core.field.QM31) values row
          let values1 := index_mut_back value
          let i ← lift (Std.Usize.wrapping_add row 1#usize)
          paddingFinite hash domain state1
            values1 i (remaining-1) dependent active
        | core.result.Result.Err error =>
          ok (core.result.Result.Err error, values, state1)
      else
        let i ← lift (Std.Usize.wrapping_add row 1#usize)
        paddingFinite hash domain state values
          i (remaining-1) dependent active
termination_by remaining
decreasing_by all_goals omega

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


/-- Selective padding retains untouched active/dependent cells, including
short circuit errors, in exactly ascending row order. -/
theorem padding_extracted_finite (hash : Hash) (domain : Slice U8) (n : Nat)
    (row dependent : Usize) (values : QValues)
    (active : Aeneas.Std.Array Bool 1024#usize) (state : State)
    (count : row.val+n = 1024) :
    prover_commit_reference.material_padding_owned hash domain state values row dependent active =
      paddingFinite hash domain state values row n dependent active := by
  induction n generalizing row values state with
  | zero =>
    have stop : row >= 1024#usize := by scalar_tac
    rw [prover_commit_reference.material_padding_owned, paddingFinite]
    simp only [stop, if_true]
  | succ n ih =>
    have more : ¬ row >= 1024#usize := by scalar_tac
    have next : (Usize.wrapping_add row 1#usize).val+n = 1024 := by
      rw [next_row row (by omega)]; omega
    have ih' := fun state values => ih (Usize.wrapping_add row 1#usize) values state next
    rw [prover_commit_reference.material_padding_owned, paddingFinite]
    simp only [more, if_false, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
      Nat.add_sub_cancel, lift, bind_tc_ok, ih']
    rfl

#print axioms next_row
#print axioms padding_extracted_finite
#print axioms columns_extracted_finite
#print axioms sub_one
#print axioms extracted_finite
#print axioms qm_extracted_finite
end R1Z.ProverCommitMaterialRecursion
