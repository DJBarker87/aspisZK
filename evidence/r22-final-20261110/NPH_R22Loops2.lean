import NPH_R22Loops
import RPu_FIq_Native04
import RPu_FIq_Native05
import RPu_FIq_Native06
import RPu_FIq_Native09
import RPu_FIq_Native10
import RPu_FIq_Native13
import RPu_FIq_Native14
import RPv_ArrayFromFnCopySlice
import MultiproofSortRef.Funs
import NCX_Reference.Funs
import NCV_Reference.Funs

/-! NPH_ (R22 item 4, second batch). Two kinds of result, both reusing the generic
`AspisR1.NPH_R22Loops.usize_succ_ok`.

TOTAL (a): five pure loop bodies whose only checked arithmetic is the guarded `i + 1` and
whose other steps are in-bounds indexing; each is proved checked-ok for every input.

Guarded step (for judgment (c)): for the remaining bodies, the body's only overflow-checked
operation (by the body read recorded with its normalised hash in NPH_R22_CONE.json) is one
`x + 1#usize` under the body's own guard; the lemma `<name>_step` proves that increment safe
whenever the guard holds, stated with the guard exactly as the gate body writes it. Indexing,
`Array.update`, comparisons and `&&` are not overflow-checks (bounds checks are on in both
profiles), and callees are separate cone definitions with their own R22 judgment.
Standard axioms; no merged module is changed. -/
set_option autoImplicit false
namespace AspisR1.NPH_R22Loops2
open Aeneas Aeneas.Std Result AspisR1.NPH_R22Loops

/-! ### TOTAL bodies -/

/-- TOTAL: NCX_Reference.zero_loop.body, every input. -/
theorem ncx_zero_loop_body_total (b : Slice U8) (i : Usize) :
    ∃ v, NCX_Reference.zero_loop.body b i = ok v := by
  unfold NCX_Reference.zero_loop.body
  by_cases hi : i < Slice.len b
  · have hlen : i.val < b.length := by
      have := hi
      first | (simpa [Slice.len_val] using this) | (simp only [Slice.len] at this; exact this) | scalar_tac | exact this
    obtain ⟨m, hm, _⟩ := WP.spec_imp_exists (Slice.index_usize_spec b i hlen)
    obtain ⟨z, hz, _⟩ := usize_succ_ok i (Slice.len b) hi
    simp only [hi, ↓reduceIte, hm, bind_tc_ok]
    split
    · exact ⟨_, rfl⟩
    · simp only [hz, bind_tc_ok]; exact ⟨_, rfl⟩
  · simp only [hi, ↓reduceIte]; exact ⟨_, rfl⟩

/-- TOTAL: NCV_Reference.zero_loop.body, every input. -/
theorem ncv_zero_loop_body_total (b : Slice U8) (i : Usize) :
    ∃ v, NCV_Reference.zero_loop.body b i = ok v := by
  unfold NCV_Reference.zero_loop.body
  by_cases hi : i < Slice.len b
  · have hlen : i.val < b.length := by
      have := hi
      first | (simpa [Slice.len_val] using this) | (simp only [Slice.len] at this; exact this) | scalar_tac | exact this
    obtain ⟨m, hm, _⟩ := WP.spec_imp_exists (Slice.index_usize_spec b i hlen)
    obtain ⟨z, hz, _⟩ := usize_succ_ok i (Slice.len b) hi
    simp only [hi, ↓reduceIte, hm, bind_tc_ok]
    split
    · exact ⟨_, rfl⟩
    · simp only [hz, bind_tc_ok]; exact ⟨_, rfl⟩
  · simp only [hi, ↓reduceIte]; exact ⟨_, rfl⟩

theorem len8 {α : Type} (a : Array α 8#usize) (i : Usize) (hi : i < 8#usize) : i.val < a.length := by
  have h1 : i.val < 8 := by first | (simpa using hi) | scalar_tac | exact hi
  first | (simpa [Array.length, a.property] using h1) | (simp only [Array.length, a.property]; first | exact h1 | scalar_tac) | scalar_tac

/-- TOTAL: NCV_Reference.eq_digest_loop.body, every input. -/
theorem ncv_eq_digest_loop_body_total (a b : Array U32 8#usize) (i : Usize) :
    ∃ v, NCV_Reference.eq_digest_loop.body a b i = ok v := by
  unfold NCV_Reference.eq_digest_loop.body
  by_cases hi : i < 8#usize
  · obtain ⟨m, hm, _⟩ := WP.spec_imp_exists (Array.index_usize_spec a i (len8 a i hi))
    obtain ⟨m2, hm2, _⟩ := WP.spec_imp_exists (Array.index_usize_spec b i (len8 b i hi))
    obtain ⟨z, hz, _⟩ := usize_succ_ok i 8#usize hi
    simp only [hi, ↓reduceIte, hm, hm2, bind_tc_ok]
    split
    · exact ⟨_, rfl⟩
    · simp only [hz, bind_tc_ok]; exact ⟨_, rfl⟩
  · simp only [hi, ↓reduceIte]; exact ⟨_, rfl⟩

/-- TOTAL: NCV_Reference.valid_sequences_loop.body, every input (outside both top cones; served by closed rows). -/
theorem ncv_valid_sequences_loop_body_total (seq : Array U64 8#usize) (i : Usize) :
    ∃ v, NCV_Reference.valid_sequences_loop.body seq i = ok v := by
  unfold NCV_Reference.valid_sequences_loop.body
  by_cases hi : i < 8#usize
  · obtain ⟨m, hm, _⟩ := WP.spec_imp_exists (Array.index_usize_spec seq i (len8 seq i hi))
    obtain ⟨z, hz, _⟩ := usize_succ_ok i 8#usize hi
    simp only [hi, ↓reduceIte, hm, bind_tc_ok]
    split
    · exact ⟨_, rfl⟩
    · simp only [hz, bind_tc_ok]; exact ⟨_, rfl⟩
  · simp only [hi, ↓reduceIte]; exact ⟨_, rfl⟩

/-- TOTAL: NCV_Reference.zero_sequences_loop.body, every input (outside both top cones; served by closed rows). -/
theorem ncv_zero_sequences_loop_body_total (seq : Array U64 8#usize) (i : Usize) :
    ∃ v, NCV_Reference.zero_sequences_loop.body seq i = ok v := by
  unfold NCV_Reference.zero_sequences_loop.body
  by_cases hi : i < 8#usize
  · obtain ⟨m, hm, _⟩ := WP.spec_imp_exists (Array.index_usize_spec seq i (len8 seq i hi))
    obtain ⟨z, hz, _⟩ := usize_succ_ok i 8#usize hi
    simp only [hi, ↓reduceIte, hm, bind_tc_ok]
    split
    · exact ⟨_, rfl⟩
    · simp only [hz, bind_tc_ok]; exact ⟨_, rfl⟩
  · simp only [hi, ↓reduceIte]; exact ⟨_, rfl⟩

/-! ### Guarded steps (judgment (c)); each guard is the gate body's own `if` condition -/

abbrev Step (x : Usize) : Prop := ∃ z, (x + 1#usize : Result Usize) = ok z ∧ z.val = x.val + 1

theorem ncx_equal_loop_body_step (b : Slice U8) (i : Usize) (h : i < Slice.len b) : Step i :=
  usize_succ_ok i _ h
theorem ncv_equal_loop_body_step (b : Slice U8) (i : Usize) (h : i < Slice.len b) : Step i :=
  usize_succ_ok i _ h

theorem interpolate_three_constant_columns_loop_step (lane : Usize)
    (h : lane < FIq_Native.poseidon2.POSEIDON2_WIDTH) : Step lane := usize_succ_ok lane _ h
theorem external_local_packed_raw_loop0_step (output : Usize) (h : output < 4#usize) : Step output :=
  usize_succ_ok output _ h
theorem external_local_packed_raw_loop0_loop0_step (limb : Usize) (h : limb < 4#usize) : Step limb :=
  usize_succ_ok limb _ h
theorem external_linear_lazy_loop1_step (index : Usize)
    (h : index < FIq_Native.poseidon2.POSEIDON2_WIDTH) : Step index := usize_succ_ok index _ h
theorem internal_linear_lazy_loop0_step (lane : Usize)
    (h : lane < FIq_Native.poseidon2.POSEIDON2_WIDTH) : Step lane := usize_succ_ok lane _ h
theorem pattern_values_literal_loop0_step (limb : Usize)
    (h : limb < FIq_Native.poseidon2.POSEIDON2_WIDTH) : Step limb := usize_succ_ok limb _ h
theorem pattern_values_literal_loop1_step (pattern_index : Usize)
    (h : pattern_index <
      FIq_Native.pool_v1.pair_forest_copy_terminal.POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1) :
    Step pattern_index := usize_succ_ok pattern_index _ h
theorem evaluate_with_selectors_loop_step (link_index : Usize)
    (h : link_index <
      FIq_Native.pool_v1.pair_forest_copy_terminal.POOL_V1_PAIR_FOREST_COPY_TERMINAL_LINKS_V1) :
    Step link_index := usize_succ_ok link_index _ h
theorem active_literal_loop_step (block : Usize) (h : block < 64#usize) : Step block :=
  usize_succ_ok block _ h
theorem add_value_lanes_loop0_step (index : Usize) (h : index < 10#usize) : Step index :=
  usize_succ_ok index _ h
theorem equality_value_loop_step (left : Array FIq_Native.field.QM31 10#usize) (index : Usize)
    (h : index < Slice.len (Array.to_slice left)) : Step index := usize_succ_ok index _ h
theorem array_from_fn_copy_loop_step {N : Usize} (i : Usize) (h : i < N) : Step i :=
  usize_succ_ok i _ h
theorem sort_rows_step (at1 n : Usize) (h : ¬ (at1 >= n)) : Step at1 := by
  have h' : at1.val < n.val := by
    first | exact Nat.lt_of_not_le h | (simp only [ge_iff_le, not_le] at h; exact h) | scalar_tac
  exact usize_succ_ok at1 n h'

/-- semantic_initial_and_absorption: its one checked increment is the constant
`poseidon2.RATE + 1 = 9`, safe unconditionally. -/
theorem semantic_initial_rate_succ_ok :
    ∃ z, (FIq_Native.poseidon2.RATE + 1#usize : Result Usize) = ok z ∧ z.val = 9 := by
  have hr : FIq_Native.poseidon2.RATE = 8#usize := by unfold FIq_Native.poseidon2.RATE; rfl
  rw [hr]
  have h8 : (8#usize : Usize).val < (16#usize : Usize).val := by first | decide | simp | scalar_tac
  obtain ⟨z, hz, hv⟩ := usize_succ_ok 8#usize 16#usize h8
  refine ⟨z, hz, ?_⟩
  rw [hv]; first | rfl | simp | decide

#print axioms ncx_zero_loop_body_total
#print axioms ncv_zero_loop_body_total
#print axioms ncv_eq_digest_loop_body_total
#print axioms ncv_valid_sequences_loop_body_total
#print axioms ncv_zero_sequences_loop_body_total
#print axioms ncx_equal_loop_body_step
#print axioms ncv_equal_loop_body_step
#print axioms interpolate_three_constant_columns_loop_step
#print axioms external_local_packed_raw_loop0_step
#print axioms external_local_packed_raw_loop0_loop0_step
#print axioms external_linear_lazy_loop1_step
#print axioms internal_linear_lazy_loop0_step
#print axioms pattern_values_literal_loop0_step
#print axioms pattern_values_literal_loop1_step
#print axioms evaluate_with_selectors_loop_step
#print axioms active_literal_loop_step
#print axioms add_value_lanes_loop0_step
#print axioms equality_value_loop_step
#print axioms array_from_fn_copy_loop_step
#print axioms sort_rows_step
#print axioms semantic_initial_rate_succ_ok
end AspisR1.NPH_R22Loops2
