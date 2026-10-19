import R1PrefixNextLaw
import R1PrefixPendingFacts
import R1QueryOwnFollow
import R1TraceSuffixFacts

/-! Follow an ordinary prefix and its next duplex round from a collision-free
trace, assuming explicit known-state and read facts for the records. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.PrefixNextTrace

open FS FS2 FS2.Duplex R0C.V3
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.DuplexFrames
open AspisV8R19.SourceDuplexStep

variable {M Cv : Type} {L : Nat}

theorem follows_after_prefix (p : Params M Cv L) (H : Addr L → State)
    (tr : List (Addr L × State)) (Qtot : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1)
    (hQ : firstReads emptyTable tr ≤ Qtot)
    (hold : ¬ hitsBad (badColl p Qtot) emptyTable tr)
    (c : Addr L) (hc : Read tr c)
    (hparsec : (parseAbsorb c).isSome)
    (hnewsq : Read tr (squeezeA p (H c)))
    (hnewadv : Read tr (advanceA p (H c)))
    (rs : List (Rec M))
    (hknown : ∀ r ∈ rs, ∃ b, tableBefore emptyTable tr c b = some r.2.1)
    (hprefixreads : ∀ r ∈ rs, Read tr (squeezeA p r.2.1)) :
    bfollow (PrefixNextLaw.output p (tableBefore emptyTable tr c) rs)
      (traceFrom tr c) (QueryNextLaw.own p c)
      ((PrefixAnswers.missing p (tableBefore emptyTable tr c) rs).map
        fun b => (b, none))
      (tableBefore emptyTable tr c) =
      some (completeRounds p emptyTable H 0 rs,
        (p.σ rs.length (H (squeezeA p (H c))), H (advanceA p (H c)))) := by
  let T := tableBefore emptyTable tr c
  let miss := PrefixAnswers.missing p T rs
  have hpending := PrefixPendingFacts.pending_facts p H tr Qtot hcons hQ hold
    c hc hparsec rs hknown hprefixreads
  have hsep : ∀ b ∈ miss,
      b ≠ c ∧ b ≠ squeezeA p (H c) ∧ b ≠ advanceA p (H c) := by
    intro b hb
    exact (hpending b hb).2.2
  have hmissing : ∀ b ∈ miss, T b = none ∧ Read tr b := by
    intro b hb
    exact ⟨(hpending b hb).1, (hpending b hb).2.1⟩
  have hbsq : Before tr c (squeezeA p (H c)) :=
    noColl_prefix_after p Qtot H tr hcons hQ hold c (squeezeA p (H c))
      hc hnewsq (toBytes_squeezeA p (H c))
  have hbadv : Before tr c (advanceA p (H c)) :=
    noColl_prefix_after p Qtot H tr hcons hQ hold c (advanceA p (H c))
      hc hnewadv (toBytes_advanceA p (H c))
  have hnd : (miss ++ [c, squeezeA p (H c), advanceA p (H c)]).Nodup := by
    rw [List.nodup_append]
    refine ⟨PrefixAnswers.missing_nodup p T rs, ?_, ?_⟩
    · simp [before_ne tr hbsq, before_ne tr hbadv, squeezeA_ne_advanceA p (H c)]
    · intro b hb d hd hbd
      have hbown : b ∈ [c, squeezeA p (H c), advanceA p (H c)] := by
        rw [hbd]
        exact hd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hbown
      rcases hbown with heq | heq | heq
      · exact (hsep b hb).1 heq
      · exact (hsep b hb).2.1 heq
      · exact (hsep b hb).2.2 heq
  have hfresh : ∀ b ∈ miss ++ [c, squeezeA p (H c), advanceA p (H c)],
      T b = none ∧ Read (traceFrom tr c) b := by
    intro b hb
    have hpair : T b = none ∧ Read tr b := by
      rcases List.mem_append.mp hb with hb | hb
      · exact hmissing b hb
      · rcases List.mem_cons.mp hb with heq | hb
        · subst b
          exact ⟨tableBefore_self H tr c hcons, hc⟩
        · rcases List.mem_cons.mp hb with heq | hb
          · subst b
            exact ⟨TraceSuffix.after_absent H tr c _ hcons hbsq, hnewsq⟩
          · have heq := List.mem_singleton.mp hb
            subst b
            exact ⟨TraceSuffix.after_absent H tr c _ hcons hbadv, hnewadv⟩
    exact ⟨hpair.1,
      TraceSuffix.absent_read H tr c b hcons hc hpair.2 hpair.1⟩
  have hfollow := QueryOwnFollow.follow p H (traceFrom tr c) T c miss
    (PrefixNextLaw.output p T rs)
    (TraceSuffix.traceFrom_consistent H tr c hcons hc) hnd hfresh
    (DQ.before_traceFrom c c _ tr hc (Or.inl rfl) hbsq)
    (DQ.before_traceFrom c c _ tr hc (Or.inl rfl) hbadv)
  have hT : ∀ b v, T b = some v → v = H b := by
    intro b v hcell
    exact (DuplexPrefixTable.table_consistent H tr hcons c b v hcell).1
  change bfollow (PrefixNextLaw.output p T rs) (traceFrom tr c)
    (QueryNextLaw.own p c) (miss.map fun b => (b, none)) T = _
  rw [hfollow]
  change some (PrefixNextLaw.output p T rs (H (advanceA p (H c)))
      (miss.map H ++ [H (squeezeA p (H c))])) = _
  rw [PrefixNextLaw.output_append p T rs (miss.map H)
    [H (squeezeA p (H c))] (H (advanceA p (H c))) (by simp [miss])]
  rw [PrefixAnswers.fromAnswers_map p T 0 rs H hT]
  rfl

#print axioms follows_after_prefix

end AspisR1.PrefixNextTrace
end
