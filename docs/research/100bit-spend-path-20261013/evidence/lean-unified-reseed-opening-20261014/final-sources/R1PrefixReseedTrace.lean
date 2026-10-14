import R1PrefixNextLaw
import R1PrefixPendingFacts
import R1ReseedOwnFollow
import R1ReseedTrace

/-! Complete earlier ordinary records while following a current round with
the explicit opening-domain reseed. The additional tail-state collision
exclusion is charged separately by the existing combined collision bound. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.PrefixReseedTrace

open FS FS2 FS2.Duplex R0C.V3
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.DuplexFrames
open AspisV8R19.SourceDuplexStep

variable {M Cv : Type} {L : Nat}

theorem follows_after_prefix (p : Params M Cv L) (tag : Byte) (hL : 62 ≤ L)
    (H : Addr L → State) (tr : List (Addr L × State)) (Qtot : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1)
    (hQ : firstReads emptyTable tr ≤ Qtot)
    (hold : ¬ hitsBad (badColl p Qtot) emptyTable tr)
    (htail : ¬ hitsBad (ParsedStateCollision.bad TrailingStateFrame.tailState Qtot)
      emptyTable tr)
    (c : Addr L) (hc : Read tr c)
    (hparsec : (parseAbsorb c).isSome)
    (hnewsq : Read tr (squeezeA p (H c)))
    (hnewadv : Read tr (advanceA p (H c)))
    (hreseed : Read tr (OpeningReseedFrame.addr tag hL (H (advanceA p (H c)))))
    (rs : List (Rec M))
    (hknown : ∀ r ∈ rs, ∃ b, tableBefore emptyTable tr c b = some r.2.1)
    (hprefixreads : ∀ r ∈ rs, Read tr (squeezeA p r.2.1)) :
    bfollow (PrefixNextLaw.output p (tableBefore emptyTable tr c) rs)
      (traceFrom tr c) (ReseedSamplerLaw.own p c (OpeningReseedFrame.addr tag hL))
      ((PrefixAnswers.missing p (tableBefore emptyTable tr c) rs).map
        fun b => (b, none))
      (tableBefore emptyTable tr c) =
      some (completeRounds p emptyTable H 0 rs,
        (p.σ rs.length (H (squeezeA p (H c))),
          H (OpeningReseedFrame.addr tag hL (H (advanceA p (H c)))))) := by
  let T := tableBefore emptyTable tr c
  let miss := PrefixAnswers.missing p T rs
  let sq := squeezeA p (H c)
  let ad := advanceA p (H c)
  let r := OpeningReseedFrame.addr tag hL (H ad)
  have hpending := PrefixPendingFacts.pending_facts p H tr Qtot hcons hQ hold
    c hc hparsec rs hknown hprefixreads
  have hasq : Before tr c sq :=
    noColl_prefix_after p Qtot H tr hcons hQ hold c sq hc hnewsq
      (toBytes_squeezeA p (H c))
  have haad : Before tr c ad :=
    noColl_prefix_after p Qtot H tr hcons hQ hold c ad hc hnewadv
      (toBytes_advanceA p (H c))
  have hadr : Before tr ad r :=
    ParsedStateTrace.parsed_after TrailingStateFrame.tailState Qtot H tr hcons hQ
      htail ad r hnewadv hreseed (OpeningReseedFrame.tailState_addr tag hL (H ad))
  have har : Before tr c r := before_trans tr haad hadr
  have hsqr : ∀ s, squeezeA p s ≠ r := by
    intro s he
    have heLen := congrArg (fun b : Addr L => b.toBytes.length) he
    have hsqLen : (squeezeA p s).toBytes.length = 33 := by
      simp [squeezeA, Addr.toBytes_ofBytes, squeeze, bytes_length]
    have hrLen : r.toBytes.length = 62 := OpeningReseedFrame.addr_length tag hL (H ad)
    omega
  have hsep : ∀ b ∈ miss, b ≠ c ∧ b ≠ sq ∧ b ≠ ad ∧ b ≠ r := by
    intro b hb
    have hp := (hpending b hb).2.2
    refine ⟨hp.1, hp.2.1, hp.2.2, ?_⟩
    have hbmap : b ∈ rs.map (fun z => squeezeA p z.2.1) :=
      (List.mem_filter.mp (List.mem_dedup.mp hb)).1
    obtain ⟨z, _, he⟩ := List.mem_map.mp hbmap
    rw [← he]
    exact hsqr z.2.1
  have hnd : (miss ++ [c, sq, ad, r]).Nodup := by
    rw [List.nodup_append]
    refine ⟨PrefixAnswers.missing_nodup p T rs, ?_, ?_⟩
    · simp [before_ne tr hasq, before_ne tr haad, before_ne tr har,
        squeezeA_ne_advanceA p (H c), hsqr (H c), before_ne tr hadr, sq, ad]
    · intro b hb d hd he
      have hbown : b ∈ [c, sq, ad, r] := by rw [he]; exact hd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hbown
      rcases hbown with he | he | he | he
      · exact (hsep b hb).1 he
      · exact (hsep b hb).2.1 he
      · exact (hsep b hb).2.2.1 he
      · exact (hsep b hb).2.2.2 he
  have hownfacts : ∀ b ∈ [c, sq, ad, r], Read tr b ∧ (b = c ∨ Before tr c b) := by
    intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact ⟨hc, Or.inl rfl⟩
    · exact ⟨hnewsq, Or.inr hasq⟩
    · exact ⟨hnewadv, Or.inr haad⟩
    · exact ⟨hreseed, Or.inr har⟩
  have hfresh : ∀ b ∈ miss ++ [c, sq, ad, r],
      T b = none ∧ Read (traceFrom tr c) b := by
    intro b hb
    have hpair : T b = none ∧ Read tr b := by
      rcases List.mem_append.mp hb with hb | hb
      · exact ⟨(hpending b hb).1, (hpending b hb).2.1⟩
      · obtain ⟨hread, hafter⟩ := hownfacts b hb
        refine ⟨?_, hread⟩
        rcases hafter with he | hbefore
        · rw [he]; exact tableBefore_self H tr c hcons
        · exact TraceSuffix.after_absent H tr c b hcons hbefore
    exact ⟨hpair.1, TraceSuffix.absent_read H tr c b hcons hc hpair.2 hpair.1⟩
  have hfollow := ReseedOwnFollow.follow p H (traceFrom tr c) T c
    (OpeningReseedFrame.addr tag hL) miss (PrefixNextLaw.output p T rs)
    (TraceSuffix.traceFrom_consistent H tr c hcons hc) hnd hfresh
    (DQ.before_traceFrom c c sq tr hc (Or.inl rfl) hasq)
    (DQ.before_traceFrom c c ad tr hc (Or.inl rfl) haad)
    (DQ.before_traceFrom c c r tr hc (Or.inl rfl) har)
    (DQ.before_traceFrom c ad r tr hc (Or.inr haad) hadr)
  have hT : ∀ b v, T b = some v → v = H b := by
    intro b v hcell
    exact (DuplexPrefixTable.table_consistent H tr hcons c b v hcell).1
  change bfollow (PrefixNextLaw.output p T rs) (traceFrom tr c)
    (ReseedSamplerLaw.own p c (OpeningReseedFrame.addr tag hL))
    (miss.map fun b => (b, none)) T = _
  rw [hfollow]
  change some (PrefixNextLaw.output p T rs (H r)
    (miss.map H ++ [H sq])) = _
  rw [PrefixNextLaw.output_append p T rs (miss.map H) [H sq] (H r) (by simp [miss]),
    PrefixAnswers.fromAnswers_map p T 0 rs H hT]
  rfl

#print axioms follows_after_prefix

end AspisR1.PrefixReseedTrace
end
