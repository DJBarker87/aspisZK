import R1OpeningPrefixTrace

/-! Expose semantic and opening table cells directly at the endpoint after
the opening prefix. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OpeningEndpointCells

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.DuplexFrames
open AspisV8R19.SourceDuplexStep

variable {M Cv : Type} {L : Nat}

theorem cells_before_next (p : Params M Cv L)
    (pubBytes : Bytes) (hlen : pubBytes.length < 2^32)
    (hL : 75 + pubBytes.length ≤ L) (c1 : State) (tag : Byte) (h62 : 62 ≤ L)
    (H : Addr L → State) (tr : List (Addr L × State)) (Qtot : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1) (hQ : firstReads emptyTable tr ≤ Qtot)
    (hold : ¬ hitsBad (badColl p Qtot) emptyTable tr)
    (htail : ¬ hitsBad (ParsedStateCollision.bad TrailingStateFrame.tailState Qtot)
      emptyTable tr)
    (semanticFuel n : Nat) (hn : 0 < n) (hsfuel : n ≤ semanticFuel)
    (ss sb : Nat → State) (sl : Nat → Byte) (sd : Nat → Bytes)
    (hsD : ∀ j, (sd j).length ≤ p.D)
    (hsroot : ss 0 = H (PublicInitFrame.addr pubBytes hL c1))
    (hi : Read tr (PublicInitFrame.addr pubBytes hL c1))
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
    T (PublicInitFrame.addr pubBytes hL c1) = some (ss 0) ∧
      (∀ j < n,
        T (absorbA p (ss j) (sl j) (sd j) (hsD j)) = some (sb j) ∧
        T (advanceA p (sb j)) = some (ss (j + 1))) ∧
      T (OpeningReseedFrame.addr tag h62 (ss n)) = some (os 0) ∧
      (∀ j < k,
        T (absorbA p (os j) (ol j) (od j) (hoD j)) = some (ob j) ∧
        T (advanceA p (ob j)) = some (os (j + 1))) := by
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
    ss sb sl sd hsD (PublicInitFrame.addr pubBytes hL c1) hsroot hi n hn
    hsabs hsstep hsar hsdr c hlastc
  obtain ⟨hseed, hocells⟩ := DuplexRecordPrefix.table_cells p H tr Qtot hcons hQ hold
    os ob ol od hoD r horoot hr k hoabs hostep hoar hodr c hc hp
  exact ⟨hinit, hscells, hseed, hocells⟩

#print axioms cells_before_next

end AspisR1.OpeningEndpointCells
end
