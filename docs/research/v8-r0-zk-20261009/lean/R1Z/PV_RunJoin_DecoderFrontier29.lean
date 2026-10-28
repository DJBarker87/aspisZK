import R1Z.PV_RunJoin_DecoderDigestLoop29
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_DecoderFrontier29
open Aeneas Aeneas.Std Result ControlFlow R0Z.WriterRefine
open AspisR1TerminalDecoder.pool_v1.pair_tree_profile
open PV_RunJoin_DecoderDigestLoop29
local instance (p : Prop) : Decidable p := Classical.propDecidable p
abbrev Frontier := Array (Array U32 8#usize) 20#usize

theorem digest_result (d : Array U32 8#usize) :
    digest_is_canonical d = ok (decide (Canon8 d)) := by
  rw [digest_is_canonical,correct d 0#usize (by decide)]
  congr 2
  apply propext
  simp only [PV_RunJoin_DecoderDigestLoop29.Tail,UScalar.ofNatCore_val_eq,Canon8]
  exact ⟨fun h j hj => h j (Nat.zero_le j) hj,fun h j _ hj => h j hj⟩
#print axioms digest_result

theorem body_in_range (a : Frontier) (i : Usize) (hi : i.val < 20) :
    validate_pool_v1_pair_live_snapshot_v1_loop.body a i =
      if Canon8 a.val[i.val]! then
        (do let j ← i + 1#usize; ok (cont j))
      else ok (done (.Err PoolV1PairLiveSnapshotErrorV1.NonCanonicalDigest)) := by
  unfold validate_pool_v1_pair_live_snapshot_v1_loop.body
  simp only [Array.to_slice,Slice.len,lift,bind_tc_ok]
  rw [if_pos (by simpa [UScalar.lt_equiv] using hi)]
  rw [index_ok_gen a i (by simpa using hi)]
  simp only [bind_tc_ok]
  rw [digest_result]
  simp only [bind_tc_ok,decide_eq_true_eq]
#print axioms body_in_range

theorem body_done (a : Frontier) (i : Usize) (hi : 20 ≤ i.val) :
    validate_pool_v1_pair_live_snapshot_v1_loop.body a i = ok (done (.Ok ())) := by
  unfold validate_pool_v1_pair_live_snapshot_v1_loop.body
  simp only [Array.to_slice,Slice.len,lift,bind_tc_ok]
  rw [if_neg (by simpa [UScalar.lt_equiv] using (show ¬i.val < 20 by omega))]
#print axioms body_done

def Tail (a : Frontier) (n : Nat) : Prop := ∀ l, n ≤ l → l < 20 → Canon8 a.val[l]!

theorem frontier_loop (a : Frontier) (i : Usize) (hi : i.val ≤ 20) :
    validate_pool_v1_pair_live_snapshot_v1_loop a i =
      ok (if Tail a i.val then .Ok () else .Err PoolV1PairLiveSnapshotErrorV1.NonCanonicalDigest) := by
  generalize he : 20-i.val = remaining
  induction remaining using Nat.strong_induction_on generalizing i with
  | h remaining ih =>
    unfold validate_pool_v1_pair_live_snapshot_v1_loop
    rw [loop.eq_def]
    by_cases hlt : i.val < 20
    · rw [body_in_range a i hlt]
      by_cases hc : Canon8 a.val[i.val]!
      · rw [if_pos hc]
        obtain ⟨j,hj,hv⟩ := advance i hlt
        rw [hj]
        simp only [bind_tc_ok]
        change validate_pool_v1_pair_live_snapshot_v1_loop a j = _
        rw [ih (20-j.val) (by omega) j (by omega) rfl]
        have ht : Tail a j.val ↔ Tail a i.val := by
          constructor
          · intro h k hk hk20
            by_cases heq : k=i.val
            · simpa only [heq] using hc
            · exact h k (by omega) hk20
          · intro h k hk hk20
            exact h k (by omega) hk20
        rw [propext ht]
      · rw [if_neg hc]
        simp only [bind_tc_ok]
        have ht : ¬ Tail a i.val := fun h => hc (h i.val (by omega) hlt)
        rw [if_neg ht]
    · rw [body_done a i (by omega)]
      simp only [bind_tc_ok]
      have ht : Tail a i.val := by intro k hk hk20; omega
      rw [if_pos ht]
#print axioms frontier_loop
end R1Z.PV_RunJoin_DecoderFrontier29
