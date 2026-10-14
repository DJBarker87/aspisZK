import R1MerkleRecordedTargets
import R1ParsedTargetsPrefixHit

/-! A child target fixed in the earlier byte log is covered by the existing
finite-family first-read event when a later read, absent from that earlier
byte log, returns it. The supplied root is deliberately a separate case. -/
set_option autoImplicit false
namespace AspisR1.MerklePrefixHit

open FS FS2.Duplex
open AspisV8R19.SourceDuplexStep
open MerkleTable MerkleRecordedLog MerkleRecordedTargets

variable {L : Nat}

theorem root_or_child_hit (Qtot : Nat) (H : Addr L → State)
    (pre post : List (Addr L × State))
    (hcons : ∀ q ∈ pre ++ post, q.2 = H q.1)
    (hQ : firstReads emptyTable (pre ++ post) ≤ Qtot)
    (root : State) (a : Addr L) (ha : Read post a)
    (habsent : a.toBytes ∉ (byteLog pre).map Prod.fst)
    (htarget : H a ∈ targets (nodes (byteLog pre)) root) :
    H a = root ∨
      hitsBad (ParsedTargetsCollision.bad MerkleChildTargets.pred Qtot)
        emptyTable (pre ++ post) := by
  rcases target_cases pre root (H a) htarget with hroot | ⟨b, hb, j, hp⟩
  · exact Or.inl hroot
  · right
    exact ParsedTargetsPrefixHit.prefix_hit MerkleChildTargets.pred Qtot H pre post
      hcons hQ a b ha (absent_bytes_not_read pre a habsent) hb j hp

#print axioms root_or_child_hit

end AspisR1.MerklePrefixHit
