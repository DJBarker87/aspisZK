import R1Z.PV_RunJoin_ExternalBlocksCopy
set_option autoImplicit false
namespace R1Z.PV_RunJoin_ExternalSums
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open BuilderRecordsArray
abbrev State := Array U32 16#usize
abbrev Sums := Array U64 4#usize

def word (state : State) (c : Nat) : U64 :=
  U64.wrapping_add
    (U64.wrapping_add
      (U64.wrapping_add (UScalar.cast .U64 state.val[c]!) (UScalar.cast .U64 state.val[c+4]!))
      (UScalar.cast .U64 state.val[c+8]!))
    (UScalar.cast .U64 state.val[c+12]!)

def target (state : State) : Sums := tabulate 4#usize (word state)

theorem word_value (state : State) (c : Nat) :
    (word state c).val = state.val[c]!.val + state.val[c+4]!.val +
      state.val[c+8]!.val + state.val[c+12]!.val :=
  sum4_val _ _ _ _

/-- Exact source sums, by a four-write prior induction. No arithmetic table,
input canonicality, callee-success or source callback hypothesis is used. -/
theorem loop (state : State) (sums : Sums) (col : Usize) (hc : col.val ≤ 4)
    (prior : Prefix sums (target state) col.val) :
    AspisBuilderPoseidonReference.poseidon2.builder_reference.external_owned_loop1 state sums col =
      ok (target state) := by
  generalize he : 4-col.val = remaining
  induction remaining using Nat.strong_induction_on generalizing sums col with
  | h remaining ih =>
    rw [AspisBuilderPoseidonReference.poseidon2.builder_reference.external_owned_loop1]
    by_cases hit : col.val < 4
    · rw [if_pos (by simpa [UScalar.lt_equiv] using hit),index_ok state col (by simp;omega)]
      simp only [lift,bind_tc_ok]
      have a4 : (Usize.wrapping_add col 4#usize).val = col.val+4 := by rw [uadd _ _ (by simp;omega)];rfl
      have a8 : (Usize.wrapping_add col 8#usize).val = col.val+8 := by rw [uadd _ _ (by simp;omega)];rfl
      have a12 : (Usize.wrapping_add col 12#usize).val = col.val+12 := by rw [uadd _ _ (by simp;omega)];rfl
      rw [index_ok state _ (by rw [a4];simp;omega)]
      simp only [lift,bind_tc_ok]
      rw [index_ok state _ (by rw [a8];simp;omega)]
      simp only [lift,bind_tc_ok]
      rw [index_ok state _ (by rw [a12];simp;omega)]
      simp only [lift,bind_tc_ok]
      rw [update_gen _ col _ (by simpa using hit)]
      simp only [lift,bind_tc_ok,a4,a8,a12]
      change AspisBuilderPoseidonReference.poseidon2.builder_reference.external_owned_loop1 state
        (sums.set col (word state col.val)) (Usize.wrapping_add col 1#usize) = _
      have value : word state col.val = (target state).val[col.val]! :=
        (tabulate_get _ _ _ (by simpa using hit)).symm
      rw [value]
      have hn := next_val col (by omega)
      apply ih (4-(Usize.wrapping_add col 1#usize).val) (by omega)
        _ (Usize.wrapping_add col 1#usize) (by omega)
      · simpa only [hn] using prefix_step sums (target state) col (by simpa using hit) prior
      · rfl
    · rw [if_neg (by simpa [UScalar.lt_equiv] using hit)]
      have equal : col.val = (4#usize : Usize).val := by simp;omega
      rw [prefix_done sums (target state) (by simpa only [equal] using prior)]

theorem entry (state : State) :
    AspisBuilderPoseidonReference.poseidon2.builder_reference.external_owned_loop1 state
      (Array.repeat 4#usize 0#u64) 0#usize = ok (target state) :=
  loop state _ _ (by simp) (by intro j hj; simp at hj)

/-- Raw U64 sums lift to the same four field additions. This statement needs
no characteristic premise because the sums do not overflow. -/
theorem field_value {K : Type} [Field K] (state : State) (c : Fin 4) :
    (((target state).val[c.val]!).val : K) =
      liftN state c.val + liftN state (c.val+4) + liftN state (c.val+8) + liftN state (c.val+12) := by
  rw [target,tabulate_get _ _ _ c.isLt,word_value]
  simp only [Nat.cast_add,liftN,liftU]

#print axioms word_value
#print axioms loop
#print axioms entry
#print axioms field_value
end R1Z.PV_RunJoin_ExternalSums
