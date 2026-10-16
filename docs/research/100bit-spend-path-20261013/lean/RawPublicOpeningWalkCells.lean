import RawPublicOpeningWalk
import R1ReseedSeparation
import InitialPublicWalkCells

/-! Instantiate the public-independent opening walk from chronological table
cells. The strict reseed and initial-frame parsers recover the public; it is
not an input to the selector. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawPublicOpeningWalkCells

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.DuplexFrames
open AspisV8R19.SourceDuplexStep
variable {M Cv : Type} {L : Nat}

theorem walk_of_cells (p : Params M Cv L)
    (pub : UnifiedSampler.Public L) (hlen : pub.pubBytes.length < 2^32)
    (htag : pub.tag = 2) (c1 : State) (tag : Byte) (h62 : 62 ≤ L)
    (T : Table (Addr L) State) (H : Addr L → State)
    (tr : List (Addr L × State)) (Q : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1) (hQ : firstReads emptyTable tr ≤ Q)
    (hcoll : ¬ hitsBad (badColl p Q) emptyTable tr)
    (hT : ∀ a v, T a = some v → v = H a ∧ Read tr a)
    (n : Nat) (hn : 0 < n) (hsfuel : n ≤ 27)
    (ss sb : Nat → State) (sl : Nat → Byte) (sd : Nat → Bytes)
    (hsD : ∀ j, (sd j).length ≤ p.D)
    (hsroot : ss 0 = H (PublicInitFrame.addr pub.pubBytes pub.initFits c1))
    (hi : Read tr (PublicInitFrame.addr pub.pubBytes pub.initFits c1))
    (hsabs : ∀ j < n, sb j = H (absorbA p (ss j) (sl j) (sd j) (hsD j)))
    (hsstep : ∀ j < n, ss (j + 1) = H (advanceA p (sb j)))
    (hsar : ∀ j < n, Read tr (absorbA p (ss j) (sl j) (sd j) (hsD j)))
    (hsdr : ∀ j < n, Read tr (advanceA p (sb j)))
    (hinit : T (PublicInitFrame.addr pub.pubBytes pub.initFits c1) = some (ss 0))
    (hsacells : ∀ j < n,
      T (absorbA p (ss j) (sl j) (sd j) (hsD j)) = some (sb j))
    (hsdcells : ∀ j < n, T (advanceA p (sb j)) = some (ss (j + 1)))
    (hr : Read tr (OpeningReseedFrame.addr tag h62 (ss n)))
    (hreseed : StrictReseedDecoder.recover tag T
      (H (OpeningReseedFrame.addr tag h62 (ss n))) =
        some (OpeningReseedFrame.addr tag h62 (ss n), ss n))
    (openingFuel k : Nat) (hok : k ≤ openingFuel)
    (os ob : Nat → State) (ol : Nat → Byte) (od : Nat → Bytes)
    (hoD : ∀ j, (od j).length ≤ p.D)
    (horoot : os 0 = H (OpeningReseedFrame.addr tag h62 (ss n)))
    (hoabs : ∀ j < k, ob j = H (absorbA p (os j) (ol j) (od j) (hoD j)))
    (hostep : ∀ j < k, os (j + 1) = H (advanceA p (ob j)))
    (hoar : ∀ j < k, Read tr (absorbA p (os j) (ol j) (od j) (hoD j)))
    (hodr : ∀ j < k, Read tr (advanceA p (ob j)))
    (hoacells : ∀ j < k,
      T (absorbA p (os j) (ol j) (od j) (hoD j)) = some (ob j))
    (hodcells : ∀ j < k, T (advanceA p (ob j)) = some (os (j + 1))) :
    RawPublicOpeningWalk.walk p T tag openingFuel (os k) =
      some ((pub,c1), CarryLast.apply (os 0) (InitialPublicWalk.records ss sb sl sd n) ++
        InitialWalk.records os ob ol od k) := by
  have hinitCells := InitialPublicWalkCells.walk_of_cells p pub hlen htag c1 H tr Q
    hcons hQ hcoll T hT 27 n hn hsfuel ss sb sl sd hsD hsroot
    hsabs hsstep hinit hsacells hsdcells
  have hbase : RawPublicOpeningWalk.base p T tag (os 0) =
      some ((pub,c1), CarryLast.apply (os 0) (InitialPublicWalk.records ss sb sl sd n)) := by
    have hrec := RawPublicOpeningWalk.base_of_recovered_reseed p T tag (os 0)
      (ss n) (OpeningReseedFrame.addr tag h62 (ss n)) pub c1
      (InitialPublicWalk.records ss sb sl sd n) (by simpa only [horoot] using hreseed)
      hinitCells
    simpa only [RawPublicOpeningWalk.base, horoot] using hrec
  apply RawPublicOpeningWalk.walk_of_lookups p T tag openingFuel k os ob ol od
    pub c1 (CarryLast.apply (os 0) (InitialPublicWalk.records ss sb sl sd n)) hok
  · intro j hj
    rw [hostep j hj]
    apply DuplexRewind.unique_advance p T H tr Q hcons hQ hcoll (ob j)
    · simpa only [hostep j hj] using hodcells j hj
    · exact hT
  · intro j hj
    refine ⟨absorbA p (os j) (ol j) (od j) (hoD j), ?_, parseAbsorb_absorbA ..⟩
    rw [hoabs j hj]
    apply ReseedBoundary.findCell_correct p H tr Q hcons hQ hcoll T hT
    simpa only [hoabs j hj] using hoacells j hj
  · exact hbase
  · intro j hj hjle
    have hpred : j - 1 < k := by omega
    have hcell : T (advanceA p (ob (j - 1))) = some
        (H (advanceA p (ob (j - 1)))) := by
      simpa only [hostep (j - 1) hpred] using hodcells (j - 1) hpred
    have hnone := ReseedSeparation.recover_advance_none p H tr Q
      hcons hQ hcoll T hT tag (ob (j - 1)) hcell
    have hstate : os j = H (advanceA p (ob (j - 1))) := by
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ j)] using
        hostep (j - 1) hpred
    simpa only [RawPublicOpeningWalk.base,hstate,hnone]

#print axioms walk_of_cells
end AspisR1.RawPublicOpeningWalkCells
end
