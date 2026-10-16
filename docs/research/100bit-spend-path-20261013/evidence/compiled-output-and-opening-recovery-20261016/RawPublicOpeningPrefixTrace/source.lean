import RawPublicOpeningWalkCells
import R1StrictReseedDecoder

/-! The ordinary opening prefix and its entire preceding semantic prefix
are recovered from the table before the following absorb. Both special hash
edges are explicit. Raw row payloads still require a protocol codec instance. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawPublicOpeningPrefixTrace
open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.DuplexFrames
open AspisV8R19.SourceDuplexStep
variable {M Cv : Type} {L : Nat}

theorem walk_before_next (p : Params M Cv L)
    (pub : UnifiedSampler.Public L) (hlen : pub.pubBytes.length < 2^32)
    (htag : pub.tag = 2) (c1 : State)
    (tag : Byte) (h62 : 62 ≤ L)
    (H : Addr L → State) (tr : List (Addr L × State)) (Qtot : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1) (hQ : firstReads emptyTable tr ≤ Qtot)
    (hold : ¬ hitsBad (badColl p Qtot) emptyTable tr)
    (htail : ¬ hitsBad (ParsedStateCollision.bad TrailingStateFrame.tailState Qtot)
      emptyTable tr)
    (n : Nat) (hn : 0 < n) (hsfuel : n ≤ 27)
    (ss sb : Nat → State) (sl : Nat → Byte) (sd : Nat → Bytes)
    (hsD : ∀ j, (sd j).length ≤ p.D)
    (hsroot : ss 0 = H (PublicInitFrame.addr pub.pubBytes pub.initFits c1))
    (hi : Read tr (PublicInitFrame.addr pub.pubBytes pub.initFits c1))
    (hsabs : ∀ j < n, sb j = H (absorbA p (ss j) (sl j) (sd j) (hsD j)))
    (hsstep : ∀ j < n, ss (j + 1) = H (advanceA p (sb j)))
    (hsar : ∀ j < n, Read tr (absorbA p (ss j) (sl j) (sd j) (hsD j)))
    (hsdr : ∀ j < n, Read tr (advanceA p (sb j)))
    (hr : Read tr (OpeningReseedFrame.addr tag h62 (ss n)))
    (openingFuel k : Nat) (hofuel : k ≤ openingFuel)
    (os ob : Nat → State) (ol : Nat → Byte) (od : Nat → Bytes)
    (hoD : ∀ j, (od j).length ≤ p.D)
    (horoot : os 0 = H (OpeningReseedFrame.addr tag h62 (ss n)))
    (hoabs : ∀ j < k, ob j = H (absorbA p (os j) (ol j) (od j) (hoD j)))
    (hostep : ∀ j < k, os (j + 1) = H (advanceA p (ob j)))
    (hoar : ∀ j < k, Read tr (absorbA p (os j) (ol j) (od j) (hoD j)))
    (hodr : ∀ j < k, Read tr (advanceA p (ob j)))
    (c : Addr L) (hc : Read tr c) (hp : c.toBytes.take 32 = bytes (os k)) :
    let T := tableBefore emptyTable tr c
    RawPublicOpeningWalk.walk p T tag openingFuel (os k) =
      some ((pub,c1), CarryLast.apply (os 0) (InitialPublicWalk.records ss sb sl sd n) ++
        InitialWalk.records os ob ol od k) := by
  dsimp only
  let T := tableBefore emptyTable tr c
  let r := OpeningReseedFrame.addr tag h62 (ss n)
  let last := advanceA p (sb (n - 1))
  have hs : ss n = H last := by
    simpa only [last, Nat.sub_add_cancel (show 1 ≤ n by omega)] using
      hsstep (n - 1) (by omega)
  have htailr : TrailingStateFrame.tailState r = some (H last) := by
    simpa only [r, hs] using OpeningReseedFrame.tailState_addr tag h62 (ss n)
  have hlastread : Read tr last := hsdr (n - 1) (by omega)
  have hlastseed := ParsedStateTrace.parsed_after TrailingStateFrame.tailState Qtot H tr
    hcons hQ htail last r hlastread hr htailr
  have hseedc := (DuplexRecordPrefix.before_endpoint p H tr Qtot hcons hQ hold
    os ob ol od hoD r horoot hr k hoabs hostep hoar hodr c hc hp).1
  have hlastc := before_trans tr hlastseed hseedc
  obtain ⟨hinit, hscells⟩ := DuplexRecordAnchor.table_cells p H tr Qtot hcons hQ hold
    ss sb sl sd hsD (PublicInitFrame.addr pub.pubBytes pub.initFits c1) hsroot hi n hn
    hsabs hsstep hsar hsdr c hlastc
  obtain ⟨hseed, hocells⟩ := DuplexRecordPrefix.table_cells p H tr Qtot hcons hQ hold
    os ob ol od hoD r horoot hr k hoabs hostep hoar hodr c hc hp
  have hT : ∀ b v, T b = some v → v = H b ∧ Read tr b :=
    DuplexPrefixTable.table_consistent H tr hcons c
  have hcell : T r = some (H r) := by simpa only [horoot] using hseed
  have hrecover := StrictReseedDecoder.recover_of_cell p H tr Qtot hcons hQ hold T hT
    tag h62 (ss n) hcell
  simpa only [horoot] using RawPublicOpeningWalkCells.walk_of_cells p pub hlen
    htag c1 tag h62 T H tr Qtot hcons hQ hold hT
    n hn hsfuel ss sb sl sd hsD
    hsroot hi hsabs hsstep hsar hsdr hinit (fun j hj => (hscells j hj).1)
    (fun j hj => (hscells j hj).2) hr (by simpa only [horoot] using hrecover)
    openingFuel k hofuel os ob ol od hoD horoot hoabs hostep hoar hodr
    (fun j hj => (hocells j hj).1) (fun j hj => (hocells j hj).2)

#print axioms walk_before_next
end AspisR1.RawPublicOpeningPrefixTrace
end
