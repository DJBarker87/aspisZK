import BinRawByteCollisionTargets
import R1QuerySamplerBridge
import R1QueryContinuation

set_option autoImplicit false
noncomputable section
namespace AspisR1.RWireRawCutLiteralQueryOrder

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.AdaptiveFirstReadLaw
open AspisR1.BinRawByteCollisionTargets

theorem root_before_chain
    {M Cv : Type} {L : Nat} (p : Params M Cv L) (H : Bytes → State)
    (tr : List (Bytes × State)) (Q : Nat)
    (iv : State)
    (hcons : ∀ q ∈ tr, q.2 = H q.1)
    (hQ : firstReads emptyTable tr ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad iv BinRawByteCollisionTargets.pred Q)
      emptyTable tr)
    (c : Bytes) (hc : Read tr c) (s : Nat → State)
    (hroot : s 0 = H c)
    (hstep : ∀ j < 7, s (j + 1) = H ((advanceA p (s j)).toBytes))
    (hreads : ∀ k < 8,
      Read tr (squeezeA p (s k)).toBytes ∧ Read tr (advanceA p (s k)).toBytes) :
    ∀ k < 8,
      Before tr c (squeezeA p (s k)).toBytes ∧
      Before tr c (advanceA p (s k)).toBytes := by
  have hadj (j : Nat) (hj : j + 1 < 8) :
      Before tr (advanceA p (s j)).toBytes (squeezeA p (s (j + 1))).toBytes ∧
      Before tr (advanceA p (s j)).toBytes (advanceA p (s (j + 1))).toBytes := by
    have hadv := (hreads j (by omega)).2
    have hsq := (hreads (j + 1) hj).1
    have hadv' := (hreads (j + 1) hj).2
    have hps : (squeezeA p (s (j + 1))).toBytes.take 32 =
        bytes (H ((advanceA p (s j)).toBytes)) := by
      rw [toBytes_squeezeA, hstep j (by omega)]
    have hpa : (advanceA p (s (j + 1))).toBytes.take 32 =
        bytes (H ((advanceA p (s j)).toBytes)) := by
      rw [toBytes_advanceA, hstep j (by omega)]
    exact ⟨duplex_state_before_frame iv H tr Q
        (by exact hcons) hQ hout _ _ hadv hsq hps,
      duplex_state_before_frame iv H tr Q
        (by exact hcons) hQ hout _ _ hadv hadv' hpa⟩
  intro k
  induction k with
  | zero =>
      intro hk
      have hsq := (hreads 0 hk).1
      have hadv := (hreads 0 hk).2
      have hps : (squeezeA p (s 0)).toBytes.take 32 = bytes (H c) := by
        rw [toBytes_squeezeA, hroot]
      have hpa : (advanceA p (s 0)).toBytes.take 32 = bytes (H c) := by
        rw [toBytes_advanceA, hroot]
      exact ⟨duplex_state_before_frame iv H tr Q hcons hQ hout c _
          hc hsq hps,
        duplex_state_before_frame iv H tr Q hcons hQ hout c _
          hc hadv hpa⟩
  | succ k ih =>
      intro hk
      have hprev := ih (by omega)
      have hnext := hadj k hk
      exact ⟨before_trans tr hprev.2 hnext.1,
        before_trans tr hprev.2 hnext.2⟩

#print axioms root_before_chain

end AspisR1.RWireRawCutLiteralQueryOrder
end
