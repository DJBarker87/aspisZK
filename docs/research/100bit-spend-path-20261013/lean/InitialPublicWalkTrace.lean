import InitialPublicWalkCells
import R1DuplexRecordPrefix

/-! Recover the actual public statement and ordinary prefix from its next
first-read table by reusing the existing whole-trace cell theorem. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.InitialPublicWalkTrace
open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.DuplexFrames
open AspisV8R19.SourceDuplexStep
variable {M Cv : Type} {L : Nat}

theorem walk_before_next (p : Params M Cv L)
    (pub : UnifiedSampler.Public L) (hlen : pub.pubBytes.length < 2^32)
    (htag : pub.tag = 2) (c1 : State)
    (H : Addr L → State) (tr : List (Addr L × State)) (Qtot : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1) (hQ : firstReads emptyTable tr ≤ Qtot)
    (hold : ¬ hitsBad (badColl p Qtot) emptyTable tr)
    (fuel n : Nat) (hn : 0 < n) (hle : n ≤ fuel)
    (s absorbed : Nat → State) (label : Nat → Byte) (data : Nat → Bytes)
    (hD : ∀ j, (data j).length ≤ p.D)
    (hroot : s 0 = H (PublicInitFrame.addr pub.pubBytes pub.initFits c1))
    (hi : Read tr (PublicInitFrame.addr pub.pubBytes pub.initFits c1))
    (habs : ∀ j < n, absorbed j = H (absorbA p (s j) (label j) (data j) (hD j)))
    (hstep : ∀ j < n, s (j + 1) = H (advanceA p (absorbed j)))
    (har : ∀ j < n, Read tr (absorbA p (s j) (label j) (data j) (hD j)))
    (hdr : ∀ j < n, Read tr (advanceA p (absorbed j)))
    (c : Addr L) (hc : Read tr c)
    (hp : c.toBytes.take 32 = bytes (s n)) :
    InitialPublicWalk.walk p (tableBefore emptyTable tr c) fuel (s n) =
      some ((pub,c1), InitialWalk.records s absorbed label data n) := by
  obtain ⟨hinit, hcells⟩ := DuplexRecordPrefix.table_cells p H tr Qtot hcons hQ hold
    s absorbed label data hD (PublicInitFrame.addr pub.pubBytes pub.initFits c1) hroot hi n
    habs hstep har hdr c hc hp
  exact InitialPublicWalkCells.walk_of_cells p pub hlen htag c1 H tr Qtot hcons hQ hold
    (tableBefore emptyTable tr c) (DuplexPrefixTable.table_consistent H tr hcons c)
    fuel n hn hle s absorbed label data hD hroot habs hstep hinit
    (fun j hj => (hcells j hj).1) (fun j hj => (hcells j hj).2)

#print axioms walk_before_next
end AspisR1.InitialPublicWalkTrace
end
