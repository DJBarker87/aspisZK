import R1QueryMissingFacts
import R1TableStateSeparation
import R1TraceSuffixFacts
import R1QueryOwnFollow
import R1QueryAnswersFirstRead
import R1JointNextLaw
import R1PrefixPendingFacts

/-! Trace following for an ordinary prefix, q22 query recovery, and the
following duplex round. Shared pending cells use a single deduplicated answer
list. The ordinary records must satisfy explicit known-state and read facts;
this theorem is not a full protocol decoder or Fiat--Shamir instantiation. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.JointNextTrace
open FS FS2 FS2.Duplex R0C.V3
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.DuplexFrames
open AspisV8R19.SourceDuplexStep
variable {M Cv : Type} {L : Nat}

theorem follows_after_prefix_query (p : Params M Cv L) (H : Addr L → State)
    (tr : List (Addr L × State)) (Qtot : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1)
    (hQ : firstReads emptyTable tr ≤ Qtot)
    (hcoll : ¬ hitsBad (badColl p Qtot) emptyTable tr)
    (s : Nat → State)
    (hstep : ∀ j < 8, s (j + 1) = H (advanceA p (s j)))
    (hreadadv : ∀ j < 8, Read tr (advanceA p (s j)))
    (hreadsq : ∀ j < 8, Read tr (squeezeA p (s j)))
    (a c : Addr L) (haread : Read tr a) (hcread : Read tr c)
    (hparsea : (parseAbsorb a).isSome) (hparsec : (parseAbsorb c).isSome)
    (hroot : s 0 = H a)
    (hprefix : c.toBytes.take 32 = bytes (QueryFirstRead.result p H s).2)
    (hnewsq : Read tr (squeezeA p (H c)))
    (hnewadv : Read tr (advanceA p (H c))) (i : Nat)
    (rs : List (Rec M))
    (hknown : ∀ r ∈ rs, ∃ b, tableBefore emptyTable tr c b = some r.2.1)
    (hprefixreads : ∀ r ∈ rs, Read tr (squeezeA p r.2.1)) :
    bfollow
      (JointNextLaw.output p (tableBefore emptyTable tr c) rs (QueryFirstRead.result p H s).2 i)
      (traceFrom tr c) (QueryNextLaw.own p c)
      ((JointPrefixAnswers.missing p (tableBefore emptyTable tr c) rs (QueryFirstRead.result p H s).2).map
        fun b => (b, none))
      (tableBefore emptyTable tr c) =
      some ((completeRounds p emptyTable H 0 rs, some (a, QueryFirstRead.result p H s)),
        (p.σ i (H (squeezeA p (H c))), H (advanceA p (H c)))) := by
  let T := tableBefore emptyTable tr c
  let endpoint := (QueryFirstRead.result p H s).2
  let qmiss := QueryDecoder.missing p T endpoint
  let miss := JointPrefixAnswers.missing p T rs endpoint
  obtain ⟨k, hk, hselected, hseek, _⟩ :=
    QueryFirstRead.recover_query_before_endpoint p H tr Qtot hcons hQ hcoll
      s hstep hreadadv a c haread hcread hparsea hroot hprefix
  have hmem : ∀ b ∈ qmiss, ∃ j < k + 1, b = squeezeA p (s j) ∧ T b = none := by
    intro b hb
    exact QueryDecoder.missing_mem_states p T endpoint a s (k + 1) hseek b hb
  have hstates : ∀ j < k + 1, s j ≠ H c :=
    TableStateSeparation.prefix_states_ne_endpoint p H tr Qtot hcons hQ hcoll
      s (k + 1) (fun j hj => hstep j (by omega))
      (fun j hj => hreadadv j (by omega)) a c haread hcread hroot
      (by rw [← hselected]; exact hprefix)
  have hqsep : ∀ b ∈ qmiss,
      b ≠ c ∧ b ≠ squeezeA p (H c) ∧ b ≠ advanceA p (H c) := by
    intro b hb
    obtain ⟨j, hj, rfl, _⟩ := hmem b hb
    refine ⟨?_, ?_, squeezeA_ne_advanceA' p (s j) (H c)⟩
    · intro heq
      have hn : parseAbsorb c = none := by
        rw [← heq]
        exact QueryDecoder.parseAbsorb_squeeze_none p (s j)
      rw [hn] at hparsec
      contradiction
    · intro heq
      exact hstates j hj (squeezeA_injective p heq)
  have hpending := PrefixPendingFacts.pending_facts p H tr Qtot hcons hQ hcoll
    c hcread hparsec rs hknown hprefixreads
  have hsep : ∀ b ∈ miss,
      b ≠ c ∧ b ≠ squeezeA p (H c) ∧ b ≠ advanceA p (H c) := by
    intro b hb
    rcases JointPrefixAnswers.missing_cases p T rs endpoint b hb with hp | hq
    · exact (hpending b hp).2.2
    · exact hqsep b hq
  have hmissing : ∀ b ∈ miss, T b = none ∧ Read tr b := by
    intro b hb
    rcases JointPrefixAnswers.missing_cases p T rs endpoint b hb with hp | hq
    · exact ⟨(hpending b hp).1, (hpending b hp).2.1⟩
    · obtain ⟨j, hj, rfl, hn⟩ := hmem b hq
      exact ⟨hn, hreadsq j (by omega)⟩
  have hbsq : Before tr c (squeezeA p (H c)) :=
    noColl_prefix_after p Qtot H tr hcons hQ hcoll c (squeezeA p (H c))
      hcread hnewsq (toBytes_squeezeA p (H c))
  have hbadv : Before tr c (advanceA p (H c)) :=
    noColl_prefix_after p Qtot H tr hcons hQ hcoll c (advanceA p (H c))
      hcread hnewadv (toBytes_advanceA p (H c))
  have hnd : (miss ++ [c, squeezeA p (H c), advanceA p (H c)]).Nodup := by
    rw [List.nodup_append]
    refine ⟨JointPrefixAnswers.missing_nodup p T rs endpoint, ?_, ?_⟩
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
        · rw [heq]
          exact ⟨tableBefore_self H tr c hcons, hcread⟩
        · rcases List.mem_cons.mp hb with heq | hb
          · rw [heq]
            exact ⟨TraceSuffix.after_absent H tr c _ hcons hbsq, hnewsq⟩
          · have hb' := List.mem_singleton.mp hb
            rw [hb']
            exact ⟨TraceSuffix.after_absent H tr c _ hcons hbadv, hnewadv⟩
    exact ⟨hpair.1, TraceSuffix.absent_read H tr c b hcons hcread hpair.2 hpair.1⟩
  have hfollow := QueryOwnFollow.follow p H (traceFrom tr c) T c miss
    (JointNextLaw.output p T rs endpoint i)
    (TraceSuffix.traceFrom_consistent H tr c hcons hcread) hnd hfresh
    (DQ.before_traceFrom c c _ tr hcread (Or.inl rfl) hbsq)
    (DQ.before_traceFrom c c _ tr hcread (Or.inl rfl) hbadv)
  change bfollow (JointNextLaw.output p T rs endpoint i) (traceFrom tr c)
    (QueryNextLaw.own p c) (miss.map fun b => (b, none)) T = _
  rw [hfollow, JointNextLaw.output_append p T rs endpoint i (miss.map H)
    [H (squeezeA p (H c))] (H (advanceA p (H c))) (by simp [miss])]
  rw [JointPrefixAnswers.fromAnswers_map p T rs endpoint H
    (fun b v hb => (DuplexPrefixTable.table_consistent H tr hcons c b v hb).1)]
  rw [QueryDecoder.recover_correct_on_missing p H tr Qtot hcons hQ hcoll s hstep hreadadv
    a c haread hcread hparsea hroot hprefix H (fun _ _ => rfl)]
  rfl

#print axioms follows_after_prefix_query
end AspisR1.JointNextTrace
end
