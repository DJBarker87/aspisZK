import R1Z.PV_RunJoin_BankAbsorb18
set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankBlock18
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1
open PV_RunJoin_BankRow17
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary

theorem block (columns : Columns) (block : Usize) (absorbed states : Nat → State)
    (initial_reads : ∀ lane : Usize, lane.val < 16 →
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U32)
        columns.val[lane.val]! (Usize.wrapping_mul block 16#usize) = ok (absorbed 0).val[lane.val]!)
    (absorb_step : ∀ lane : Usize, lane.val < 8 → ∃ word sum,
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U32)
        columns.val[lane.val]! (Usize.wrapping_add (Usize.wrapping_mul block 16#usize) 12#usize) = ok word ∧
      aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! word = ok sum ∧
      (absorbed lane.val).set lane sum = absorbed (lane.val+1))
    (hstart : states 0 = absorbed 8)
    (pair : ∀ n : Usize, n.val < 11 → ∃ first,
      poseidon2.evaluate_trace_round_pair (states n.val) n = ok (some (first,states (n.val+1))))
    (round_reads : ∀ n : Usize, n.val < 11 → ∀ lane : Usize, lane.val < 16 →
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U32)
        columns.val[lane.val]! (rowIndex block (Usize.wrapping_add n 1#usize)) =
          ok (states (n.val+1)).val[lane.val]!)
    (padding_reads : ∀ n : Usize, 13 ≤ n.val → n.val < 16 → ∀ lane : Usize, lane.val < 16 →
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U32)
        columns.val[lane.val]! (rowIndex block n) =
          ok (Array.repeat 16#usize aspis_core.field.M31.ZERO).val[lane.val]!) :
    pair_forest_trace.validate_forest_poseidon_block columns block = ok (.Ok ()) := by
  rw [pair_forest_trace.validate_forest_poseidon_block]
  simp only [lift,bind_tc_ok]
  rw [PV_RunJoin_BankInitial18.initial columns _ _ initial_reads]
  simp only [bind_tc_ok]
  rw [poseidon2.RATE]
  have hab := PV_RunJoin_BankAbsorb18.absorb columns _ absorbed absorb_step ⟨0#usize,8#usize⟩ rfl (by simp)
  change pair_forest_trace.validate_forest_poseidon_block_loop0 ⟨0#usize,8#usize⟩ columns (Usize.wrapping_mul block 16#usize) (absorbed 0) = ok (absorbed 8) at hab
  rw [hab]
  simp only [bind_tc_ok]
  rw [← hstart]
  have hround := PV_RunJoin_BankRounds18.rounds columns block states pair round_reads 0#usize (by simp)
  change pair_forest_trace.validate_forest_poseidon_block_loop1 columns block (states 0) (.Ok ()) 0#usize = ok (.Ok ()) at hround
  rw [hround]
  simp only [bind_tc_ok]
  exact PV_RunJoin_BankRounds18.padding columns block padding_reads 13#usize (by simp) (by simp)
#print axioms block
end R1Z.PV_RunJoin_BankBlock18
