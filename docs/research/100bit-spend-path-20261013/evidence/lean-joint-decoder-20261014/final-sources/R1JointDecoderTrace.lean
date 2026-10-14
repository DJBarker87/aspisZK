import R1OpeningQueryTrace
import R1JointDecoder
import R1PrefixRecordLength

/-! The joint address/table decoder succeeds on the actual canonical query
and following-round messages, under the existing explicit trace premises. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.JointDecoderTrace
open FS FS2 FS2.Duplex R0C.V3
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.DuplexFrames
open AspisV8R19.SourceDuplexStep
variable {M Cv : Type} {L : Nat}

theorem decodes_after_prefix_query (p : Params M Cv L)
    (pubBytes : Bytes) (hpub : pubBytes.length < 2^32)
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
    (qm nm : M)
    (hqa : a = absorbA p (os k) (p.lbl (n + 1 + k)) (p.enc qm) (p.encLen qm))
    (hca : c = absorbA p (QueryFirstRead.result p H qs).2 (p.lbl (n + 1 + k + 1))
      (p.enc nm) (p.encLen nm))
    (hqroot : qs 0 = H a)
    (hnewsq : Read tr (squeezeA p (H c)))
    (hnewadv : Read tr (advanceA p (H c))) :
    let T := tableBefore emptyTable tr c
    let rs := PrefixRecordFacts.ordinary ss sb sm n os ob om k
    ∃ own pend g,
      JointDecoder.decode p pubBytes tag semanticFuel openingFuel c T = some (own, pend, g) ∧
      bfollow g (traceFrom tr c) own pend T =
        some (c1, qm, nm,
          ((completeRounds p emptyTable H 0 rs, some (a, QueryFirstRead.result p H qs)),
            (p.σ (n + 1 + k + 1) (H (squeezeA p (H c))), H (advanceA p (H c))))) := by
  dsimp only
  let T := tableBefore emptyTable tr c
  let rs := PrefixRecordFacts.ordinary ss sb sm n os ob om k
  let endpoint := (QueryFirstRead.result p H qs).2
  have hlen : rs.length = n + 1 + k :=
    PrefixRecordLength.ordinary_length ss sb sm n os ob om k
  have hparsea : parseAbsorb a = some (os k, p.lbl (n + 1 + k), p.enc qm) := by
    rw [hqa, parseAbsorb_absorbA]
  have hparsec : parseAbsorb c = some (endpoint, p.lbl (n + 1 + k + 1), p.enc nm) := by
    rw [hca, parseAbsorb_absorbA]
  have hpa : (parseAbsorb a).isSome := by rw [hparsea]; rfl
  have hpc : (parseAbsorb c).isSome := by rw [hparsec]; rfl
  have haprefix : a.toBytes.take 32 = bytes (os k) := by
    rw [hqa]
    exact toBytes_absorbA p _ _ _ _
  have hcprefix : c.toBytes.take 32 = bytes endpoint := by
    rw [hca]
    exact toBytes_absorbA p _ _ _ _
  obtain ⟨htyped, hfollow⟩ := OpeningQueryTrace.recover_and_follow
    p pubBytes hpub hL c1 tag h62 H tr Qtot hcons hQ hold htail
    semanticFuel n hsfuel ss sb sm hsD hsroot hi hsabs hsstep hsar hsdr hssq hr
    openingFuel k hofuel os ob om hoD horoot hoabs hostep hoar hodr hosq
    qs hqstep hqadv hqsq a c ha hc hpa hpc haprefix hqroot hcprefix hnewsq hnewadv
  obtain ⟨j, hj, hselected, hseek, _⟩ := QueryFirstRead.recover_query_before_endpoint
    p H tr Qtot hcons hQ hold qs hqstep hqadv a c ha hc hpa hqroot hcprefix
  let ctx : JointContext.Context M L := ⟨endpoint, a, c1, rs, qm, nm⟩
  have hcontext : JointContext.parse p pubBytes tag semanticFuel openingFuel c T = some ctx :=
    JointContext.parse_of_checks p pubBytes tag semanticFuel openingFuel c T endpoint _ _
      a _ (os k) _ _ c1 rs qm nm hparsec hseek hparsea htyped
      (by rw [hlen]; exact IndexedMessage.read_encoded p (n + 1 + k) qm)
      (by rw [hlen]; exact IndexedMessage.read_encoded p (n + 1 + k + 1) nm)
  refine ⟨QueryNextLaw.own p c,
    (JointPrefixAnswers.missing p T rs endpoint).map (fun b => (b, none)),
    JointDecoder.output p T ctx,
    JointDecoder.decode_of_parse p pubBytes tag semanticFuel openingFuel c T ctx hcontext, ?_⟩
  have hf := JointDecoder.follows_of_joint p T ctx c (traceFrom tr c)
    ((completeRounds p emptyTable H 0 rs, some (a, QueryFirstRead.result p H qs)),
      (p.σ (n + 1 + k + 1) (H (squeezeA p (H c))), H (advanceA p (H c))))
    (by simpa only [ctx, hlen] using hfollow)
  exact hf

#print axioms decodes_after_prefix_query
end AspisR1.JointDecoderTrace
end
