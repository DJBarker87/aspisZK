import R1Z.PV_RunJoin_DecoderFrontier29
import R1Z.PV_RunJoin_DecoderReturn29
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_DecodedFrontier29
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open AspisR1TerminalDecoder.pool_v1.pair_tree_profile
open PV_RunJoin_DecoderFrontier29

/-- The actual snapshot validator's success forces every frontier word to
be canonical, including active slots. This uses symbolic loop correctness. -/
theorem validated_frontier (snapshot : PoolV1PairLiveSnapshotV1)
    (h : validate_pool_v1_pair_live_snapshot_v1 snapshot = ok (.Ok ())) :
    ∀ l : Fin 20, Canon8 snapshot.frontier.val[l.val]! := by
  unfold validate_pool_v1_pair_live_snapshot_v1 at h
  pv_peel h with poolZero hp
  cases poolZero <;> simp only [Bool.false_eq_true,↓reduceIte] at h
  · pv_peel h with domainZero hd
    cases domainZero <;> simp only [Bool.false_eq_true,↓reduceIte] at h
    · split at h
      · cases h
      · pv_peel h with capacity hc
        split at h
        · cases h
        · pv_peel h with rootCanon hr
          cases rootCanon <;> simp only [Bool.false_eq_true,↓reduceIte] at h
          · cases h
          · rw [frontier_loop snapshot.frontier 0#usize (by decide)] at h
            have ht : PV_RunJoin_DecoderFrontier29.Tail snapshot.frontier (0#usize).val := by
              by_contra hn
              rw [if_neg hn] at h
              cases h
            intro l
            exact ht l.val (by change 0 ≤ l.val; omega) l.isLt
    · cases h
  · cases h
#print axioms validated_frontier

/-- Canonical-route provenance at the actual extracted decoder. No encoded
snapshot supplied by a caller is silently substituted for its return. -/
theorem decoded_frontier (bytes : Slice U8) (snapshot : PoolV1PairLiveSnapshotV1)
    (h : decode_pool_v1_pair_live_snapshot_v1 bytes = ok (.Ok snapshot)) :
    ∀ l : Fin 20, Canon8 snapshot.frontier.val[l.val]! :=
  validated_frontier snapshot (PV_RunJoin_DecoderReturn29.validated bytes snapshot h)
#print axioms decoded_frontier
end R1Z.PV_RunJoin_DecodedFrontier29
