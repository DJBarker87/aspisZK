import R1OpeningAnchorCells
import R1OpeningPrefixCompletion
import R1PrefixRecordFacts
import R1JointNextTrace

/-! Recover the ordinary prefix from the table before the round following
q22, then follow that prefix, q22, and the next round with one shared pending
answer set. This is an abstract codec/trace theorem, not a Rust refinement or
a full Fiat--Shamir instance. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OpeningQueryTrace
open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.DuplexFrames
open AspisV8R19.SourceDuplexStep
variable {M Cv : Type} {L : Nat}

theorem recover_and_follow (p : Params M Cv L)
    (pubBytes : Bytes) (hlen : pubBytes.length < 2^32)
    (hL : 75 + pubBytes.length ≤ L) (c1 : State) (tag : Byte) (h62 : 62 ≤ L)
    (H : Addr L → State) (tr : List (Addr L × State)) (Qtot : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1) (hQ : firstReads emptyTable tr ≤ Qtot)
    (hold : ¬ hitsBad (badColl p Qtot) emptyTable tr)
    (htail : ¬ hitsBad (ParsedStateCollision.bad TrailingStateFrame.tailState Qtot)
      emptyTable tr)
    (semanticFuel n : Nat) (hsfuel : n + 1 ≤ semanticFuel)
    (ss sb : Nat → State) (sm : Nat → M)
    (hsD : ∀ j, (p.enc (sm j)).length ≤ p.D)
    (hsroot : ss 0 = H (PublicInitFrame.addr pubBytes hL c1))
    (hi : Read tr (PublicInitFrame.addr pubBytes hL c1))
    (hsabs : ∀ j < n + 1, sb j = H (absorbA p (ss j) (p.lbl j) (p.enc (sm j)) (hsD j)))
    (hsstep : ∀ j < n + 1, ss (j + 1) = H (advanceA p (sb j)))
    (hsar : ∀ j < n + 1, Read tr (absorbA p (ss j) (p.lbl j) (p.enc (sm j)) (hsD j)))
    (hsdr : ∀ j < n + 1, Read tr (advanceA p (sb j)))
    (hssq : ∀ j < n + 1, Read tr (squeezeA p (sb j)))
    (hr : Read tr (OpeningReseedFrame.addr tag h62 (ss (n + 1))))
    (openingFuel k : Nat) (hofuel : k ≤ openingFuel)
    (os ob : Nat → State) (om : Nat → M)
    (hoD : ∀ j, (p.enc (om j)).length ≤ p.D)
    (horoot : os 0 = H (OpeningReseedFrame.addr tag h62 (ss (n + 1))))
    (hoabs : ∀ j < k, ob j = H
      (absorbA p (os j) (p.lbl (n + 1 + j)) (p.enc (om j)) (hoD j)))
    (hostep : ∀ j < k, os (j + 1) = H (advanceA p (ob j)))
    (hoar : ∀ j < k, Read tr
      (absorbA p (os j) (p.lbl (n + 1 + j)) (p.enc (om j)) (hoD j)))
    (hodr : ∀ j < k, Read tr (advanceA p (ob j)))
    (hosq : ∀ j < k, Read tr (squeezeA p (ob j)))
    (qs : Nat → State)
    (hqstep : ∀ j < 8, qs (j + 1) = H (advanceA p (qs j)))
    (hqadv : ∀ j < 8, Read tr (advanceA p (qs j)))
    (hqsq : ∀ j < 8, Read tr (squeezeA p (qs j)))
    (a c : Addr L) (ha : Read tr a) (hc : Read tr c)
    (hparsea : (parseAbsorb a).isSome) (hparsec : (parseAbsorb c).isSome)
    (haprefix : a.toBytes.take 32 = bytes (os k))
    (hqroot : qs 0 = H a)
    (hcprefix : c.toBytes.take 32 = bytes (QueryFirstRead.result p H qs).2)
    (hnewsq : Read tr (squeezeA p (H c)))
    (hnewadv : Read tr (advanceA p (H c))) :
    let T := tableBefore emptyTable tr c
    let rs := PrefixRecordFacts.ordinary ss sb sm n os ob om k
    OpeningPrefixCompletion.typed p pubBytes tag T semanticFuel openingFuel (os k) =
        some (c1, rs) ∧
      bfollow
        (JointNextLaw.output p T rs (QueryFirstRead.result p H qs).2 (n + 1 + k + 1))
        (traceFrom tr c) (QueryNextLaw.own p c)
        ((JointPrefixAnswers.missing p T rs (QueryFirstRead.result p H qs).2).map
          fun b => (b, none)) T =
        some ((completeRounds p emptyTable H 0 rs, some (a, QueryFirstRead.result p H qs)),
          (p.σ (n + 1 + k + 1) (H (squeezeA p (H c))), H (advanceA p (H c)))) := by
  dsimp only
  let T := tableBefore emptyTable tr c
  let rs := PrefixRecordFacts.ordinary ss sb sm n os ob om k
  obtain ⟨j, hj, hselected, _, _⟩ := QueryFirstRead.recover_query_before_endpoint
    p H tr Qtot hcons hQ hold qs hqstep hqadv a c ha hc hparsea hqroot hcprefix
  have hqcells := DuplexPrefixTable.table_cells p H tr Qtot hcons hQ hold qs (j + 1)
    (fun t ht => hqstep t (by omega)) (fun t ht => hqadv t (by omega))
    c a hc ha (by rw [← hselected]; exact hcprefix) hqroot
  have hac : Before tr a c :=
    TableBeforeOrder.before_of_cell H tr hcons c a (qs 0) hqcells.1
  have hwalk := OpeningPrefixAnchor.walk_before_anchor p pubBytes hlen hL c1 tag h62
    H tr Qtot hcons hQ hold htail semanticFuel (n + 1) (by omega) hsfuel
    ss sb p.lbl (fun t => p.enc (sm t)) hsD hsroot hi hsabs hsstep hsar hsdr hr
    openingFuel k hofuel os ob (fun t => p.lbl (n + 1 + t)) (fun t => p.enc (om t))
    hoD horoot hoabs hostep hoar hodr a c ha haprefix hac
  have hcells := OpeningAnchorCells.cells_before_anchor p pubBytes hlen hL c1 tag h62
    H tr Qtot hcons hQ hold htail semanticFuel (n + 1) (by omega) hsfuel
    ss sb p.lbl (fun t => p.enc (sm t)) hsD hsroot hi hsabs hsstep hsar hsdr hr
    openingFuel k hofuel os ob (fun t => p.lbl (n + 1 + t)) (fun t => p.enc (om t))
    hoD horoot hoabs hostep hoar hodr a c ha haprefix hac
  have hknown : ∀ r ∈ rs, ∃ b, T b = some r.2.1 :=
    PrefixRecordFacts.ordinary_known T ss sb sm n os ob om k
      (fun t ht => ⟨absorbA p (ss t) (p.lbl t) (p.enc (sm t)) (hsD t),
        (hcells.2.1 t ht).1⟩)
      (fun t ht => ⟨absorbA p (os t) (p.lbl (n + 1 + t)) (p.enc (om t)) (hoD t),
        (hcells.2.2.2 t ht).1⟩)
  have hreads : ∀ r ∈ rs, Read tr (squeezeA p r.2.1) :=
    PrefixRecordFacts.ordinary_reads p tr ss sb sm n os ob om k hssq hosq
  constructor
  · exact OpeningPrefixCompletion.typed_of_walk p pubBytes tag T semanticFuel openingFuel
      (os k) c1 ss sb sm n os ob om k hwalk
  · exact JointNextTrace.follows_after_prefix_query p H tr Qtot hcons hQ hold
      qs hqstep hqadv hqsq a c ha hc hparsea hparsec hqroot hcprefix hnewsq hnewadv
      (n + 1 + k + 1) rs hknown hreads

#print axioms recover_and_follow
end AspisR1.OpeningQueryTrace
end
