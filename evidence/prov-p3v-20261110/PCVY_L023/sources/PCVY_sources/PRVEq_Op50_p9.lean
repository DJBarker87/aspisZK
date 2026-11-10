import Aeneas
import NCV_Reference.Funs
import PCVV_LaneDecodeRef
import PRVEq_Op50_p8
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
noncomputable section
namespace PCVY_Op50
open PCVV_LaneDecodeRef (sl le)

/-- `DecidableEq` for the Aeneas digest arrays: equality of the underlying lists -/
instance instDecEqDig : DecidableEq (Std.Array U32 8#usize) := fun a b =>
  decidable_of_iff (a.val = b.val) ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

theorem dec_arr (a b : Std.Array U32 8#usize) : decide (a = b) = decide (a.val = b.val) := by
  by_cases h : a.val = b.val
  · have : a = b := Subtype.ext h
    simp [h]
  · have : a ≠ b := fun e => h (congrArg Subtype.val e)
    simp [h, this]

/-- The instantiation of the transcription's constants K by the frozen crate values
(r1_pool_adapter.rs 448-520; pair_forest_accounts.rs, incremental_merkle.rs, format.rs,
pair_tree_profile.rs, v7_pair_empty_roots.rs); see PCVY_TRANSCRIPTION_REVIEW.md. -/
def K0 : PCVV_LaneDecodeRef.K (Std.Array U32 8#usize) where
  accountBytes := 768
  laneMagic := [65, 83, 76, 56]
  laneVersion := 2
  laneCount := 8
  treeDepth := 20
  accountFormatBinding := [65, 83, 80, 73, 83, 70, 79, 82, 69, 83, 84, 56, 2, 2, 2, 8, 1, 20, 1,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  headerBytes := 80
  treeStateMagic := [65, 83, 80, 84]
  treeStateVersion := 1
  treeHashVersion := 3
  digestEncodingVersion := 1
  pairCapacity := 1048576
  emptyRoots := fun i => NCV_Reference.EMPTY.val.getD i (Array.repeat 8#usize 0#u32)
  decodeDigest := decDig

theorem idx_arrG {α : Type} {n : Usize} (a : Std.Array α n) (i : Usize) (h : i.val < a.val.length) :
    a.index_usize i = ok (a.val[i.val]'h) := by
  obtain ⟨x, hx, hv⟩ := WP.spec_imp_exists (Array.index_usize_spec a i h)
  rw [hx, hv]

theorem empty_len : NCV_Reference.EMPTY.val.length = 21 := by
  have := NCV_Reference.EMPTY.property; simpa using this

theorem empty_get (level : Nat) (h : level < 21) :
    K0.emptyRoots level = NCV_Reference.EMPTY.val[level]'(by rw [empty_len]; exact h) := by
  show NCV_Reference.EMPTY.val.getD level _ = _
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [empty_len]; exact h)]
  rfl

theorem shr_val (next : U64) (level : Usize) (h : level.val < 64) :
    ∃ i2 : U64, (next >>> level : Result U64) = ok i2 ∧ i2.val = next.val >>> level.val := by
  obtain ⟨z, hz, hv⟩ := WP.spec_imp_exists (U64.ShiftRight_spec next level h)
  exact ⟨z, hz, hv.1⟩

theorem and1_val (x : U64) : (x &&& 1#u64).val = x.val &&& 1 := by
  rw [UScalar.val_and]; simp

theorem eq0_iff (x : U64) : (x = 0#u64) ↔ x.val = 0 :=
  ⟨fun h => by rw [h]; simp, fun h => UScalar.eq_of_val_eq (by rw [h]; simp)⟩

theorem lt20 (i : Usize) (h : i.val < 20) : i < 20#usize := by scalar_tac
theorem not_lt20 (i : Usize) (h : ¬ i.val < 20) : ¬ (i < 20#usize) := by scalar_tac

theorem flen (F : Std.Array (Std.Array U32 8#usize) 20#usize) : F.val.length = 20 := by
  have := F.property; simpa using this

theorem fr_body_end (tree : Slice U8) (next : U64) (F : Std.Array (Std.Array U32 8#usize) 20#usize)
    (level : Usize) (h : ¬ level.val < 20) :
    NCV_Reference.decode_frontier_loop.body tree next F level = ok (done (core.result.Result.Ok F)) := by
  have hge := not_lt20 level h
  unfold NCV_Reference.decode_frontier_loop.body
  simp only [hge, if_false]

theorem th_val : (32#usize).val = 32 := by simp
theorem fo_val : (48#usize).val = 48 := by simp

theorem fr_body (tree : Slice U8) (hlen : 688 ≤ tree.val.length) (next : U64)
    (F : Std.Array (Std.Array U32 8#usize) 20#usize) (level : Usize) (hl : level.val < 20) :
    (decDig (sl (bytesOf tree) (48 + 32 * level.val) (48 + 32 * level.val + 32)) = none →
      NCV_Reference.decode_frontier_loop.body tree next F level =
        ok (done (core.result.Result.Err ()))) ∧
    (∀ val, decDig (sl (bytesOf tree) (48 + 32 * level.val) (48 + 32 * level.val + 32)) = some val →
      (((next.val >>> level.val) &&& 1 == 0 && val != K0.emptyRoots level.val) = true →
        NCV_Reference.decode_frontier_loop.body tree next F level =
          ok (done (core.result.Result.Err ()))) ∧
      (((next.val >>> level.val) &&& 1 == 0 && val != K0.emptyRoots level.val) = false →
        ∀ c : Usize, (level + 1#usize : Result Usize) = ok c →
          NCV_Reference.decode_frontier_loop.body tree next F level =
            ok (cont (F.set level val, c)))) := by
  have hb := tree.property
  have hlt := lt20 level hl
  obtain ⟨i, e32, v32⟩ := mul_ok 32#usize level (by rw [th_val]; scalar_tac)
  obtain ⟨i1, e48, v48⟩ := add_ok 48#usize i (by rw [fo_val, v32, th_val]; scalar_tac)
  have hi1 : i1.val = 48 + 32 * level.val := by rw [v48, v32, fo_val, th_val]
  have hs : i1.val + 32 ≤ tree.val.length := by omega
  have hdig := digest_eq tree i1 hs
  rw [hi1] at hdig
  have hia : level.val < F.val.length := by rw [flen]; exact hl
  refine ⟨fun hd => ?_, fun val hd => ?_⟩
  · unfold NCV_Reference.decode_frontier_loop.body
    simp only [hlt, if_true, bind_tc_ok, e32, e48, hdig, hd,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame.from, core.convert.FromSame]
    try rfl
  · obtain ⟨⟨x, back⟩, hm, hxb⟩ := WP.spec_imp_exists (Array.index_mut_usize_spec F level hia)
    obtain ⟨i2, hs2, hv2⟩ := shr_val next level (by omega)
    have hE : NCV_Reference.EMPTY.index_usize level =
        ok (NCV_Reference.EMPTY.val[level.val]'(by rw [empty_len]; omega)) :=
      idx_arrG _ _ _
    have hemp : K0.emptyRoots level.val =
        NCV_Reference.EMPTY.val[level.val]'(by rw [empty_len]; omega) := empty_get _ (by omega)
    have hback : back = F.set level := hxb.2
    have hq := eq_digest_eq val (NCV_Reference.EMPTY.val[level.val]'(by rw [empty_len]; omega))
    have hi3 : (i2 &&& 1#u64).val = (next.val >>> level.val) &&& 1 := by rw [and1_val, hv2]
    constructor
    · intro hc
      simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hc
      obtain ⟨hA, hB⟩ := hc
      have hA' : (i2 &&& 1#u64) = 0#u64 := (eq0_iff _).2 (by rw [hi3]; exact hA)
      have hB' : ¬ val.val = (NCV_Reference.EMPTY.val[level.val]'(by rw [empty_len]; omega)).val := by
        intro h; apply hB; rw [hemp]; exact Subtype.ext h
      unfold NCV_Reference.decode_frontier_loop.body
      simp only [hlt, if_true, bind_tc_ok, e32, e48, hdig, hd,
        core.result.Result.Insts.CoreOpsTry.branch, hm, hs2, lift, hA', hE, hq,
        decide_eq_true_eq, hB', if_false]
      try rfl
    · intro hc c hcc
      simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq, bne_eq_false_iff_eq] at hc
      unfold NCV_Reference.decode_frontier_loop.body
      by_cases hA : (i2 &&& 1#u64) = 0#u64
      · have hv : val = NCV_Reference.EMPTY.val[level.val]'(by rw [empty_len]; omega) := by
          rcases hc with h | h
          · exact absurd ((eq0_iff _).1 hA |>.trans rfl ▸ (by rw [hi3] at *; omega)) (by omega)
          · rw [← hemp]; exact h
        have hv' : val.val = (NCV_Reference.EMPTY.val[level.val]'(by rw [empty_len]; omega)).val := by
          rw [← hv]
        simp only [hlt, if_true, bind_tc_ok, e32, e48, hdig, hd,
          core.result.Result.Insts.CoreOpsTry.branch, hm, hs2, lift, hA, hE, hq, hv',
          decide_true, hcc, hback]
        try rfl
      · simp only [hlt, if_true, bind_tc_ok, e32, e48, hdig, hd,
          core.result.Result.Insts.CoreOpsTry.branch, hm, hs2, lift, hA, if_false, hcc, hback]
        try rfl

#print axioms fr_body
end PCVY_Op50
