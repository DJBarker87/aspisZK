import R1QueryChainTraceFacts
import R1PrefixPendingFacts
import R1TraceSuffixFacts

/-! Follow a paired query chain while completing missing prefix answers.
The old background-follow theorem is reused with its freshness and order
premises derived from the explicit collision exclusion and read facts. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.PrefixQueryTrace

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
    (c : Addr L) (hc : Read tr c) (hparsec : (parseAbsorb c).isSome)
    (n : Nat)
    (hreads : ∀ k < n,
      Read tr (squeezeA p (QuerySampler.state p H (H c) k)) ∧
      Read tr (advanceA p (QuerySampler.state p H (H c) k)))
    (rs : List (Rec M))
    (hknown : ∀ r ∈ rs, ∃ b, tableBefore emptyTable tr c b = some r.2.1)
    (hprefixreads : ∀ r ∈ rs, Read tr (squeezeA p r.2.1))
    {C : Type} (g : List State → List State → C) :
    bfollow g (traceFrom tr c)
      (.ask c fun s => QueryBackgroundChain.chainBS p n s [s])
      ((PrefixAnswers.missing p (tableBefore emptyTable tr c) rs).map
        fun b => (b, none)) (tableBefore emptyTable tr c) =
      some (g ([H c] ++ (List.range n).map
          (fun k => QuerySampler.state p H (H c) (k + 1)))
        ((PrefixAnswers.missing p (tableBefore emptyTable tr c) rs).map H ++
          (List.range n).map (fun k => H (squeezeA p (QuerySampler.state p H (H c) k))))) := by
  let T := tableBefore emptyTable tr c
  let miss := PrefixAnswers.missing p T rs
  let chain := QueryBackgroundChain.chainBS p n (H c) [H c]
  let own : BS (Addr L) State (List State) :=
    .ask c fun s => QueryBackgroundChain.chainBS p n s [s]
  have hA := QueryChainTraceFacts.root_before p H tr Qtot hcons hQ hold c hc n hreads
  have hAD := QueryChainTraceFacts.advance_before p H tr Qtot hcons hQ hold c hc n hreads
  have hst := QueryChainTraceFacts.states_ne p H tr Qtot hcons hQ hold c hc n hreads
  have hpending := PrefixPendingFacts.pending_facts p H tr Qtot hcons hQ hold
    c hc hparsec rs hknown hprefixreads
  have hchainMem : ∀ e ∈ evs H chain, ∃ k < n,
      e.2 = squeezeA p (QuerySampler.state p H (H c) k) ∨
      e.2 = advanceA p (QuerySampler.state p H (H c) k) := by
    intro e he
    obtain ⟨k, hk, he'⟩ := QueryBackgroundChain.evs_chainBS_mem p H n (H c) [H c] e he
    refine ⟨k, hk, ?_⟩
    rcases he' with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hevs : evs H own = (true, c) :: evs H chain := rfl
  have hnd : (waiting (miss.map fun b => ((b, none) : Addr L × Option State)) ++
      (evs H own).map Prod.snd).Nodup := by
    rw [DQ.waiting_none, hevs, List.map_cons, List.nodup_append]
    refine ⟨PrefixAnswers.missing_nodup p T rs,
      List.nodup_cons.mpr ⟨?_, QueryBackgroundChain.chain_nodup p H n (H c) [H c] hst⟩, ?_⟩
    · intro hm
      obtain ⟨e, he, hea⟩ := List.mem_map.mp hm
      obtain ⟨k, hk, hcell⟩ := hchainMem e he
      rw [hea] at hcell
      rcases hcell with hcell | hcell
      · exact before_ne tr (hA k hk).1 hcell
      · exact before_ne tr (hA k hk).2 hcell
    · intro b hb d hd hbd
      rcases List.mem_cons.mp hd with hd | hd
      · exact (hpending b hb).2.2.1 (hbd.trans hd)
      · obtain ⟨e, he, hed⟩ := List.mem_map.mp hd
        obtain ⟨k, hk, hcell⟩ := hchainMem e he
        obtain ⟨r, hr, hbr, _⟩ := PrefixPendingFacts.missing_mem p T rs b hb
        rcases hknown r hr with ⟨a, hcellKnown⟩
        have hne := QueryChainTraceFacts.known_ne_state p H tr Qtot hcons hQ hold
          c hc n hreads a r.2.1 hcellKnown k hk
        have hbe : b = e.2 := hbd.trans hed.symm
        rcases hcell with hcell | hcell
        · exact hne (squeezeA_injective p (hbr.symm.trans (hbe.trans hcell)))
        · exact squeezeA_ne_advanceA' p _ _ (hbr.symm.trans (hbe.trans hcell))
  have hfresh : ∀ b ∈ waiting (miss.map fun b => ((b, none) : Addr L × Option State)) ++
      (evs H own).map Prod.snd, T b = none ∧ Read (traceFrom tr c) b := by
    intro b hb
    rw [DQ.waiting_none, hevs, List.map_cons] at hb
    have hpair : T b = none ∧ Read tr b := by
      rcases List.mem_append.mp hb with hb | hb
      · exact ⟨(hpending b hb).1, (hpending b hb).2.1⟩
      · rcases List.mem_cons.mp hb with hbc | hb
        · subst b
          exact ⟨tableBefore_self H tr c hcons, hc⟩
        · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hb
          obtain ⟨k, hk, hcell⟩ := hchainMem e he
          rcases hcell with hcell | hcell
          · rw [hcell]
            exact ⟨TraceSuffix.after_absent H tr c _ hcons (hA k hk).1, (hreads k hk).1⟩
          · rw [hcell]
            exact ⟨TraceSuffix.after_absent H tr c _ hcons (hA k hk).2, (hreads k hk).2⟩
    exact ⟨hpair.1, TraceSuffix.absent_read H tr c b hcons hc hpair.2 hpair.1⟩
  have hord : OrderOK (traceFrom tr c) (evs H own) := by
    rw [hevs]
    apply DQ.order_traceFrom tr c hc
    · refine ⟨fun _ e he => ?_, QueryBackgroundChain.order_chain p H tr n (H c) [H c] hAD⟩
      obtain ⟨k, hk, hcell⟩ := hchainMem e he
      rcases hcell with hcell | hcell
      · rw [hcell]; exact (hA k hk).1
      · rw [hcell]; exact (hA k hk).2
    · intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact Or.inl rfl
      · obtain ⟨k, hk, hcell⟩ := hchainMem e he
        rcases hcell with hcell | hcell
        · rw [hcell]; exact Or.inr (hA k hk).1
        · rw [hcell]; exact Or.inr (hA k hk).2
  have hfollow := bfollow_ok H g (traceFrom tr c) own
    (miss.map fun b => ((b, none) : Addr L × Option State)) T
    (TraceSuffix.traceFrom_consistent H tr c hcons hc) hnd hfresh hord
  have hrun : runOut H own =
      ([H c] ++ (List.range n).map (fun k => QuerySampler.state p H (H c) (k + 1)),
        (List.range n).map (fun k => squeezeA p (QuerySampler.state p H (H c) k))) :=
    QueryBackgroundChain.runOut_chainBS p H n (H c) [H c]
  rw [hrun] at hfollow
  simpa only [fill, List.map_map] using hfollow

#print axioms follows_after_prefix

end AspisR1.PrefixQueryTrace
end
